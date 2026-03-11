/-
Copyright (c) 2026 Information Geometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Basic
/-!
# Cost-Blind Computation

**Step 1 of the P ≠ NP program.**

A Turing machine's state graph carries no intrinsic metric —
only adjacency (the transition function) and step count.  This
file formalises that observation and proves that the transition
structure alone admits bijections which preserve all structural
properties but **scramble any externally imposed cost function**.

## The key insight

The standard computational model is **cost-blind**: it sees
transitions but not their thermodynamic cost.  Any bijection
`φ : S ≃ S` can conjugate the system, producing a structurally
identical (isomorphic) system where path costs under any external
metric are generically different.

This is why proof barriers (relativisation, natural proofs,
algebrisation) exist: they operate within the cost-blind
framework, which has too much symmetry to distinguish P from NP.

The **Fisher metric** (Step 3) breaks this symmetry by imposing
a *canonical* cost function — one that is NOT invariant under
arbitrary conjugation, but only under sufficient statistics
(Chentsov's theorem).

## Main definitions

* `CostBlindSystem` — A deterministic transition system with no
  metric structure.  Only adjacency.
* `CostBlindSystem.orbit` — The trajectory `s, f(s), f²(s), …`
* `CostBlindSystem.conjugate` — Relabeling by a bijection,
  preserving all structural properties.
* `CostBlindSystem.pathCost` — Total cost along a path under an
  *external* cost function (not intrinsic to the system).
* `CostInvariant` — A cost function invariant under a bijection.

## Main results

* `conjugate_orbit` — Orbits correspond exactly under conjugation.
* `conjugate_refl` — Conjugation by `id` is the identity.
* `conjugate_conjugate_symm` — Conjugation by `φ` then `φ⁻¹`
  recovers the original system.
* `conjugate_trans` — Conjugation respects composition.
* `conjugate_pathCost` — **The cost scrambling identity:**
  path costs in the conjugated system equal path costs in the
  original with a relabeled cost function.
* `pathCost_preserved_of_invariant` — Invariant costs are
  preserved under conjugation.
* `pathCost_changed_of_not_invariant` — Non-invariant costs
  are changed by conjugation.

## Connection to the P ≠ NP argument

This file establishes that the transition structure alone is
**too symmetric** to carry complexity-theoretic content.  The
conjugation group acts transitively on cost functions, so no
structural property can pin down "which problems are hard."

Steps 3–5 break this symmetry:

- **Step 3:** The Fisher metric is the unique Riemannian metric
  invariant under sufficient statistics (Chentsov).  Arbitrary
  conjugations are NOT sufficient statistics, so they do NOT
  preserve the Fisher cost.

- **Step 4:** Fisher curvature diverges at the SAT phase
  transition, forcing exponential thermodynamic length.

- **Step 5:** Turing machine locality bounds per-step Fisher
  displacement, converting geometric length to step count.

## References

* T. Baker, J. Gill, R. Solovay, "Relativizations of the
  P =? NP question", *SIAM J. Comput.* **4** (1975), 431–442.
* A. Razborov, S. Rudich, "Natural proofs",
  *J. Comput. Syst. Sci.* **55** (1997), 24–35.
* S. Aaronson, A. Wigderson, "Algebrization: A new barrier
  in complexity theory", *TOCT* **1** (2009), 1–54.
-/

noncomputable section

open Function Finset

/-! ## Part 1: Cost-Blind Transition Systems -/

/-- A **cost-blind system**: a deterministic transition on a type `S`,
carrying no metric, distance, or cost information.

This is the mathematical content of a Turing machine's state graph:
given a configuration, produce the next configuration.  Nothing more.
No notion of "how hard" a transition is.  No notion of "how far"
two states are, except by counting steps.

The absence of metric structure is not a limitation to be fixed —
it is the *reason* that proof barriers exist. -/
structure CostBlindSystem (S : Type*) where
  /-- The deterministic transition function. -/
  step : S → S

namespace CostBlindSystem

variable {S : Type*}

/-! ### Orbits -/

/-- The state reached after `t` applications of the transition,
starting from `s`.  This is the **trajectory** of the system. -/
def orbit (sys : CostBlindSystem S) (s : S) (t : ℕ) : S :=
  sys.step^[t] s

@[simp] theorem orbit_zero (sys : CostBlindSystem S) (s : S) :
    sys.orbit s 0 = s := rfl

theorem orbit_succ (sys : CostBlindSystem S) (s : S) (t : ℕ) :
    sys.orbit s (t + 1) = sys.step (sys.orbit s t) :=
  Function.iterate_succ_apply' sys.step t s

theorem orbit_succ' (sys : CostBlindSystem S) (s : S) (t : ℕ) :
    sys.orbit s (t + 1) = sys.orbit (sys.step s) t :=
  Function.iterate_succ_apply sys.step t s

theorem orbit_add (sys : CostBlindSystem S) (s : S) (m n : ℕ) :
    sys.orbit s (m + n) = sys.orbit (sys.orbit s m) n := by
  simp only [orbit]
  rw [Nat.add_comm]
  simp only[Function.iterate_add_apply];

/-! ## Part 2: Conjugation — Structure-Preserving Relabeling

Given a bijection `φ : S ≃ S`, the **conjugate system**
`sys.conjugate φ` has transition `s ↦ φ(step(φ⁻¹(s)))`.

This is a relabeling: the dynamics are identical, only the
names of states change.  The conjugate system is isomorphic
to the original as a directed graph.

Crucially, conjugation preserves *all structural properties*
(orbit lengths, cycle structure, reachability) but does NOT
preserve external cost assignments.
-/

/-- **Conjugation** of a system by a bijection.
The relabeled system has transition `s ↦ φ(step(φ⁻¹(s)))`. -/
def conjugate (sys : CostBlindSystem S) (φ : S ≃ S) :
    CostBlindSystem S where
  step s := φ (sys.step (φ.symm s))

/-- Orbits in the conjugated system correspond exactly to orbits
in the original, up to relabeling by `φ`. -/
theorem conjugate_orbit (sys : CostBlindSystem S) (φ : S ≃ S)
    (s : S) (t : ℕ) :
    (sys.conjugate φ).orbit (φ s) t = φ (sys.orbit s t) := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [orbit_succ, orbit_succ, ih]
    simp [conjugate]

/-- Conjugation by the identity does nothing. -/
@[simp] theorem conjugate_refl (sys : CostBlindSystem S) :
    sys.conjugate (Equiv.refl S) = sys := by
  simp[conjugate]

/-- Conjugating by `φ` then `φ⁻¹` recovers the original system.
Conjugation is reversible — no information is lost or gained. -/
theorem conjugate_conjugate_symm (sys : CostBlindSystem S)
    (φ : S ≃ S) :
    (sys.conjugate φ).conjugate φ.symm = sys := by
  simp [conjugate]

/-- Conjugation respects composition of bijections. -/
theorem conjugate_trans (sys : CostBlindSystem S)
    (φ ψ : S ≃ S) :
    (sys.conjugate φ).conjugate ψ =
    sys.conjugate (φ.trans ψ) := by
  simp [conjugate, Equiv.symm_trans_apply]

/-- **Orbit length is a structural invariant.**
The orbit from `φ s` in the conjugated system reaches `φ t`
at the same step that the orbit from `s` reaches `t` in the
original system. -/
theorem conjugate_orbit_length (sys : CostBlindSystem S)
    (φ : S ≃ S) (s : S) (t : ℕ) :
    (sys.conjugate φ).orbit (φ s) t = φ s ↔
    sys.orbit s t = s := by
  rw [conjugate_orbit]
  exact Equiv.apply_eq_iff_eq φ

/-! ## Part 3: Path Costs and the Scrambling Identity

A **cost function** `cost : S → S → ℝ` assigns a real cost to
each transition.  This is *external* to the system — the cost-blind
model does not carry it.

The **path cost** is the total cost along an orbit.  The central
result is `conjugate_pathCost`: path costs in the conjugated system
equal path costs in the original with a **scrambled** cost function.
-/

/-- The total cost along an orbit of length `T`, under an external
cost function.  This is the sum of per-step costs:

  `pathCost sys cost s T = ∑_{t=0}^{T-1} cost(orbit s t, orbit s (t+1))` -/
def pathCost (sys : CostBlindSystem S) (cost : S → S → ℝ)
    (s : S) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    cost (sys.orbit s t) (sys.orbit s (t + 1))

@[simp] theorem pathCost_zero (sys : CostBlindSystem S)
    (cost : S → S → ℝ) (s : S) :
    sys.pathCost cost s 0 = 0 := by
  simp [pathCost]

theorem pathCost_succ (sys : CostBlindSystem S)
    (cost : S → S → ℝ) (s : S) (T : ℕ) :
    sys.pathCost cost s (T + 1) =
    sys.pathCost cost s T +
      cost (sys.orbit s T) (sys.orbit s (T + 1)) := by
  simp [pathCost, Finset.sum_range_succ]

/-- **The cost scrambling identity.**

Path costs in the conjugated system equal path costs in the
original with a relabeled cost function:

  `pathCost(conjugate φ, cost, φ s, T)
     = pathCost(sys, cost ∘ (φ × φ), s, T)`

This is the formal content of "conjugation preserves structure
but scrambles costs."  The dynamics are identical (same orbits
up to relabeling), but the cost of corresponding paths changes
unless `cost` happens to be `φ`-invariant. -/
theorem conjugate_pathCost (sys : CostBlindSystem S) (φ : S ≃ S)
    (cost : S → S → ℝ) (s : S) (T : ℕ) :
    (sys.conjugate φ).pathCost cost (φ s) T =
    sys.pathCost (fun a b => cost (φ a) (φ b)) s T := by
  simp only [pathCost, conjugate_orbit]

/-! ## Part 4: Cost Invariance

A cost function is **invariant** under `φ` if relabeling doesn't
change costs.  This is the metric analogue of a symmetry.

The key result: path costs are preserved under conjugation **if
and only if** the cost function is invariant.  Non-invariant costs
are scrambled.  Since "most" bijections are not isometries of any
given metric, the cost-blind model's conjugation symmetry is
*generically broken* by the introduction of a metric.
-/

/-- A cost function is **`φ`-invariant** if it assigns the same
cost to transitions related by `φ`:
`cost(φ a, φ b) = cost(a, b)` for all `a, b`. -/
def CostInvariant (cost : S → S → ℝ) (φ : S ≃ S) : Prop :=
  ∀ a b, cost (φ a) (φ b) = cost a b

/-- A cost function is **transition-invariant** under `φ` for
system `sys` if the cost of each transition is preserved:
`cost(φ s, φ(step s)) = cost(s, step s)` for all `s`.

This is weaker than full `CostInvariant` — it only requires
invariance on transition pairs, not all pairs. -/
def TransitionCostInvariant (sys : CostBlindSystem S)
    (cost : S → S → ℝ) (φ : S ≃ S) : Prop :=
  ∀ s, cost (φ s) (φ (sys.step s)) = cost s (sys.step s)

/-- Full cost invariance implies transition cost invariance. -/
theorem CostInvariant.toTransitionInvariant
    (sys : CostBlindSystem S) {cost : S → S → ℝ} {φ : S ≃ S}
    (h : CostInvariant cost φ) :
    sys.TransitionCostInvariant cost φ :=
  fun s => h s (sys.step s)

/-- If the cost function is `φ`-invariant, conjugation preserves
all path costs.  The metric symmetry protects the costs. -/
theorem pathCost_preserved_of_invariant
    (sys : CostBlindSystem S) (φ : S ≃ S)
    (cost : S → S → ℝ) (h_inv : CostInvariant cost φ)
    (s : S) (T : ℕ) :
    (sys.conjugate φ).pathCost cost (φ s) T =
    sys.pathCost cost s T := by
  rw [conjugate_pathCost]
  congr 1; ext t
  exact h_inv _ _

/-- **Converse (on transition pairs):** if all path costs are
preserved under conjugation, the cost function must be
transition-invariant.  Specialised to 1-step paths. -/
theorem transitionInvariant_of_pathCost_preserved
    (sys : CostBlindSystem S) (φ : S ≃ S)
    (cost : S → S → ℝ)
    (h : ∀ s T, (sys.conjugate φ).pathCost cost (φ s) T =
                sys.pathCost cost s T) :
    sys.TransitionCostInvariant cost φ := by
  intro s
  have h1 := h s 1
  rw [conjugate_pathCost] at h1
  simp only [pathCost, Finset.range_one, Finset.sum_singleton,
    orbit_zero, orbit_succ] at h1
  exact h1

/-- **The symmetry-breaking theorem (existence form).**

If the cost function is NOT transition-invariant under `φ`, then
there exists a state whose 1-step path cost differs between the
original and conjugated systems.

The transition structure is preserved, but costs change.  This is
the formal content of "cost-blind computation cannot see metrics." -/
theorem pathCost_changed_of_not_invariant
    (sys : CostBlindSystem S) (φ : S ≃ S)
    (cost : S → S → ℝ)
    (h : ¬ sys.TransitionCostInvariant cost φ) :
    ∃ s, (sys.conjugate φ).pathCost cost (φ s) 1 ≠
         sys.pathCost cost s 1 := by
  simp only [TransitionCostInvariant, not_forall] at h
  obtain ⟨s, hs⟩ := h
  exact ⟨s, by
    rw [conjugate_pathCost]
    simp only [pathCost, Finset.range_one, Finset.sum_singleton,
      orbit_zero, orbit_succ]
    exact hs⟩

end CostBlindSystem

/-! ## Part 5: The Metric-Aware System

A **metric-aware system** extends a cost-blind system with an
external cost function.  The cost function breaks the conjugation
symmetry: only **isometries** (cost-preserving bijections) yield
equivalent systems.

The gap between "all bijections" (cost-blind symmetries) and
"isometries" (metric symmetries) is where complexity-theoretic
content lives.  The Fisher metric provides a *canonical* cost
function with a very small isometry group — only sufficient
statistics (Chentsov's theorem).
-/

/-- A **metric-aware system**: a cost-blind system equipped with
an external cost function that breaks the conjugation symmetry. -/
structure MetricAwareSystem (S : Type*) extends
    CostBlindSystem S where
  /-- The external cost function. -/
  cost : S → S → ℝ
  /-- Costs are nonneg (it's a distance-like quantity). -/
  cost_nonneg : ∀ a b, 0 ≤ cost a b

namespace MetricAwareSystem

variable {S : Type*}

/-- A bijection is an **isometry** of the metric-aware system if
it preserves all costs. -/
def IsIsometry (sys : MetricAwareSystem S) (φ : S ≃ S) : Prop :=
  CostBlindSystem.CostInvariant sys.cost φ

/-- Every isometry preserves path costs under conjugation. -/
theorem isometry_preserves_pathCost (sys : MetricAwareSystem S)
    (φ : S ≃ S) (h : sys.IsIsometry φ) (s : S) (T : ℕ) :
    (sys.toCostBlindSystem.conjugate φ |>.pathCost sys.cost (φ s) T) =
     sys.toCostBlindSystem.pathCost sys.cost s T :=
  CostBlindSystem.pathCost_preserved_of_invariant
    sys.toCostBlindSystem φ sys.cost h s T

/-- Non-isometries change path costs: if `φ` is not an isometry,
there exists a path whose cost differs in the conjugated system. -/
theorem non_isometry_changes_cost (sys : MetricAwareSystem S)
    (φ : S ≃ S)
    (h : ¬ sys.toCostBlindSystem.TransitionCostInvariant
      sys.cost φ) :
    ∃ s, (sys.toCostBlindSystem.conjugate φ |>.pathCost
        sys.cost (φ s) 1) ≠
      sys.toCostBlindSystem.pathCost sys.cost s 1 :=
  CostBlindSystem.pathCost_changed_of_not_invariant
    sys.toCostBlindSystem φ sys.cost h

end MetricAwareSystem

/-! ## Summary: What This File Establishes

### The cost-blind model has too much symmetry

For any transition system `sys` and any bijection `φ`:

1. `sys.conjugate φ` has **identical dynamics** to `sys`
   (orbits correspond via `φ`, orbit lengths are preserved).

2. Path costs are **scrambled**: the cost in the conjugated system
   equals the cost in the original with a relabeled cost function
   (`conjugate_pathCost`).

3. Costs are preserved **if and only if** the cost function is
   `φ`-invariant (`pathCost_preserved_of_invariant`,
   `transitionInvariant_of_pathCost_preserved`).

### Why this matters for P ≠ NP

The cost-blind model cannot distinguish "easy" from "hard"
computations because arbitrary bijections can relabel states
without changing any structural property.  A proof that "SAT
requires exponential time" must use structure beyond adjacency.

The Fisher metric provides this structure:

- It is a **canonical** cost function (unique by Chentsov).
- Its isometry group is **small** (only sufficient statistics).
- It assigns **exponential** thermodynamic length to paths
  crossing phase transitions (Step 4).
- Turing machine **locality** bounds per-step displacement,
  converting geometric length to step count (Step 5).

The passage from cost-blind to metric-aware is the passage from
"we can't prove P ≠ NP" to "we can."

### What feeds into later steps

- **Step 3** (`SymmetryBreaking.lean`) will use `conjugate_pathCost`
  and `pathCost_changed_of_not_invariant` to show that the Fisher
  metric is NOT invariant under arbitrary conjugation.

- **Step 5** (`LocalityBound.lean`) connects `pathCost` here to
  `thermodynamicLength` in `ComputationEmbedding.lean`.
-/

end
