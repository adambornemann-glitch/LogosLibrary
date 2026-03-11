/-
Copyright (c) 2026 Information Geometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import LogosLibrary.QuantumComputing.PvNP.ComputationEmbedding
import LogosLibrary.QuantumComputing.PvNP.SymmetryBreaking
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Curvature Divergence at the Phase Transition

**Step 4 of the P ≠ NP program.**

At the satisfiability phase transition, the Fisher information
diverges — the statistical manifold develops a **curvature
singularity**.  Any computation that crosses this singularity
(i.e., any algorithm that solves the problem) must traverse
exponential thermodynamic length.

This is the load-bearing step of the argument.  Steps 1–3
established the framework:

1. Cost-blind computation has too much symmetry.
2. Every computation traces a path on the Fisher manifold.
3. The Fisher metric breaks the cost-blind symmetry.

This file establishes the **quantitative content**: the
thermodynamic length required to solve NP-complete problems
at the phase transition is at least exponential.

## The physical picture (CORRECTED)

The Fisher–Rao distance on the finite probability simplex Δ_n
is bounded: `d_FR(p, q) ≤ π` for all `p, q`.  The simplex
lives on the positive orthant of a sphere, and π is its
diameter.  This bound is **independent of n**.

Therefore, the geodesic between "unsolved" and "solved"
distributions can be short.  The exponential barrier is NOT
about endpoint distance.

The barrier is about **restricted path length**.  A Turing
machine cannot follow the geodesic.  Each step is a pushforward
by a local transition — a tiny perturbation that moves mass
between a bounded number of configurations.  These "TM-achievable
moves" are geometrically constrained: near the phase transition,
they are nearly orthogonal to the geodesic direction.

The curvature divergence at the phase transition forces any
path composed of locally-constrained steps to take an
exponential detour through distribution space.  The geodesic
is short, but the machine can't take it.  Think of walking
from the front door to the mailbox by circumnavigating the
Earth — except the detour is forced by the geometry, not by
choice.

### Why the curvature matters

At the random k-SAT phase transition (α ≈ 4.267 for k = 3):

- The solution space **shatters** into exponentially many
  clusters separated by Hamming distance Θ(n).

- A locally-constrained path (one that moves O(1) mass per
  step) cannot jump between clusters.  It must traverse
  the high-curvature region where the Fisher metric is
  exponentially stiff.

- The allowed directions of TM pushforwards decouple from
  the geodesic direction in this region.  The TM is forced
  to take exponentially many small steps to traverse what
  the geodesic crosses in bounded distance.

This is the **bottleneck principle**: it's not that all paths
from A to B are long, but that all paths from A to B
*achievable by sequential local pushforward* are long.

## Structure of this file

**Approach A: axiomatise, then backfill.**

### Level 1: Restricted Path Barrier (`PhaseTransitionBarrier`)

A pure geometric statement: any path from input to output
distributions *with per-step displacement bounded by a
threshold* has exponential thermodynamic length.  The
threshold captures the locality constraint.

### Level 2: Curvature Origin (`CurvatureOrigin`)

The geometric explanation: curvature divergence at the
critical point forces locally-constrained paths to detour.
Constructs a `PhaseTransitionBarrier` from curvature data.

### Level 3: SAT Instantiation (`SATBarrier`)

The application to satisfiability.

## Main results

* `PhaseTransitionBarrier.length_lower_bound` —
  `𝓛[γ] ≥ exp(c·n)` for any locally-constrained path
  crossing the barrier.
* `PhaseTransitionBarrier.step_lower_bound` —
  `T ≥ exp(c·n) / Δ_max`.
* `CurvatureOrigin.toBarrier` — Curvature divergence implies
  a restricted path barrier.
* `SATBarrier.exponential_sat_steps` — The punchline for SAT.

## References

* G. Ruppeiner, "Riemannian geometry in thermodynamic
  fluctuation theory", *Rev. Mod. Phys.* **67** (1995), 605–659.
* R. Monasson, R. Zecchina et al., "Determining computational
  complexity from characteristic phase transitions",
  *Nature* **400** (1999), 133–137.
* D. Achlioptas, A. Coja-Oghlan, "Algorithmic barriers from
  phase transitions", *FOCS* (2008), 793–802.
* J. Ding, A. Sly, N. Sun, "Proof of the satisfiability
  conjecture for large k", *Ann. Math.* **196** (2022), 1–388.
-/

noncomputable section

open Finset Real BigOperators

/-! ## Part 1: The Restricted Path Barrier

A `PhaseTransitionBarrier` is a statement about **restricted
path length**: any path from input to output distributions
whose per-step displacement is bounded by `maxStepSize` has
exponential thermodynamic length.

This replaces the previous (incorrect) formulation that
asserted exponential *endpoint distance*.  The Fisher–Rao
distance on a finite simplex is bounded by π, so endpoint
distance cannot be exponential.  But the thermodynamic length
of a locally-constrained path CAN be exponential — the path
is forced to wind through high-curvature regions.

The `maxStepSize` parameter captures the locality constraint:
a Turing machine step moves O(1) mass, giving O(1) Fisher–Rao
displacement.  The barrier says: if each step is at most this
small, the total path length must be exponential.
-/

section Barrier

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- A **phase transition barrier** on a finite configuration space.

Asserts that any path from the input distribution (encoding an
unsolved problem instance) to the output distribution (encoding
the solution), with per-step Fisher–Rao displacement bounded by
`maxStepSize`, has thermodynamic length at least
`exp(growthRate · problemSize)`.

**Key conceptual point:** This is a statement about *restricted*
paths, not about *all* paths.  The geodesic (unrestricted
shortest path) may be short — bounded by π.  But a Turing
machine cannot follow the geodesic.  Its steps are local
pushforwards, geometrically constrained to move in specific
directions.  Near the phase transition, these directions are
nearly orthogonal to the geodesic, forcing an exponential
detour.

**Why this is an axiom (Approach A):**

The restricted path length bound encodes deep physics:
curvature divergence at the phase transition creates a
bottleneck that locally-constrained paths cannot shortcut.
Future work (Approach B) discharges this from explicit
calculations on the random k-SAT model. -/
structure PhaseTransitionBarrier
    (Cfg : Type*) [Fintype Cfg] [DecidableEq Cfg] where
  /-- The problem size parameter (e.g., number of variables). -/
  problemSize : ℕ
  /-- The distribution encoding "unsolved problem instance."
  For SAT: a random formula at clause ratio α_c, with no
  information about satisfying assignments. -/
  inputDist : FinDist Cfg
  /-- The distribution encoding "solved problem instance."
  For SAT: the same formula, but now the solver's state encodes
  a satisfying assignment (or UNSAT certificate). -/
  outputDist : FinDist Cfg
  /-- The exponential growth rate constant `c > 0`. -/
  growthRate : ℝ
  /-- The growth rate is positive. -/
  growthRate_pos : 0 < growthRate
  /-- The maximum per-step displacement for which the barrier
  applies.  Paths with steps larger than this are not
  constrained by the barrier.

  For Turing machines, each step has O(1) displacement, so
  `maxStepSize` can be any constant ≥ this O(1) bound.
  The barrier says: even with steps this large, you still
  need exponential total length. -/
  maxStepSize : ℝ
  /-- The step size threshold is positive. -/
  maxStepSize_pos : 0 < maxStepSize
  /-- **The barrier axiom (restricted path length).**

  Any computation path from `inputDist` to `outputDist`
  with per-step Fisher–Rao displacement ≤ `maxStepSize`
  has thermodynamic length ≥ `exp(growthRate · problemSize)`.

  This is the load-bearing axiom.  It encodes the bottleneck:
  locally-constrained paths through the phase transition
  region are forced to be exponentially long, even though
  the geodesic may be short.

  **Discharge route (Approach B):** Show that near the phase
  transition, the TM-achievable directions (pushforwards by
  local transitions) are nearly orthogonal to the geodesic
  direction.  The curvature divergence at α_c quantifies
  this orthogonality, and the integral over the bottleneck
  region gives the exponential lower bound. -/
  restricted_length_exponential :
    ∀ (γ : ComputationPath Cfg),
      γ.distAt 0 = inputDist →
      γ.distAt γ.numSteps = outputDist →
      (∀ t, t < γ.numSteps → γ.stepDisplacement t ≤ maxStepSize) →
      γ.thermodynamicLength ≥
      Real.exp (growthRate * (problemSize : ℝ))

namespace PhaseTransitionBarrier

variable (barrier : PhaseTransitionBarrier Cfg)

/-- The exponential lower bound is positive.
Immediate from `exp > 0`. -/
theorem lower_bound_pos :
    0 < Real.exp (barrier.growthRate * (barrier.problemSize : ℝ)) :=
  Real.exp_pos _

end PhaseTransitionBarrier

end Barrier

/-! ## Part 2: The Exponential Length Lower Bound

Given a `PhaseTransitionBarrier` and a `ComputationPath` that
starts at the input distribution, ends at the output distribution,
and has per-step displacement bounded by `maxStepSize`, the
thermodynamic length of the path is at least `exp(c · n)`.

This is now a direct application of the barrier axiom — the
proof infrastructure of Steps 1–3 is not needed here (it was
needed in the old version to chain through endpoint distance).
The Steps 1–3 infrastructure remains essential for the
`SeparationPrinciple` assembly in Part 3.
-/

section LengthBound

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- **The exponential thermodynamic length lower bound.**

Any computation path from the barrier's input distribution
to the barrier's output distribution, with per-step
displacement ≤ `maxStepSize`, has thermodynamic length
at least `exp(c · n)`.

  `𝓛[γ] ≥ exp(c · n)`

This is a direct consequence of the barrier axiom. -/
theorem PhaseTransitionBarrier.length_lower_bound
    (barrier : PhaseTransitionBarrier Cfg)
    (γ : ComputationPath Cfg)
    (h_start : γ.distAt 0 = barrier.inputDist)
    (h_end : γ.distAt γ.numSteps = barrier.outputDist)
    (h_steps : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ barrier.maxStepSize) :
    γ.thermodynamicLength ≥
    Real.exp (barrier.growthRate * (barrier.problemSize : ℝ)) :=
  barrier.restricted_length_exponential γ h_start h_end h_steps

end LengthBound

/-! ## Part 3: Assembly into the Separation Principle

A `PhaseTransitionBarrier` combined with a per-step displacement
bound `Δ ≤ maxStepSize` produces a `SeparationPrinciple` from
`SymmetryBreaking.lean`.

The key compatibility condition: the TM's per-step displacement
bound `Δ` must be at most `barrier.maxStepSize`.  This ensures
the barrier axiom applies to the TM's computation path.
-/

section Assembly

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- Construct a `SeparationPrinciple` from a phase transition
barrier and a per-step displacement bound.

Requires `Δ ≤ barrier.maxStepSize` so that the barrier axiom
applies to the computation path.

**All fields are discharged — no axioms here.** -/
def PhaseTransitionBarrier.toSeparationPrinciple
    (barrier : PhaseTransitionBarrier Cfg)
    (γ : ComputationPath Cfg)
    (h_start : γ.distAt 0 = barrier.inputDist)
    (h_end : γ.distAt γ.numSteps = barrier.outputDist)
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (hΔ_bound : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ Δ)
    (hΔ_compat : Δ ≤ barrier.maxStepSize) :
    SeparationPrinciple Cfg where
  path := γ
  lengthLowerBound :=
    Real.exp (barrier.growthRate * (barrier.problemSize : ℝ))
  maxDisplacement := Δ
  h_lower := barrier.length_lower_bound γ h_start h_end
    (fun t ht => le_trans (hΔ_bound t ht) hΔ_compat)
  h_disp_bound := hΔ_bound
  h_disp_pos := hΔ_pos

/-- **The exponential step count lower bound.**

For any computation crossing the phase transition barrier with
per-step displacement bounded by `Δ ≤ maxStepSize`:

  `T ≥ exp(c · n) / Δ`

**Proved** from `SeparationPrinciple.step_lower_bound`. -/
theorem PhaseTransitionBarrier.step_lower_bound
    (barrier : PhaseTransitionBarrier Cfg)
    (γ : ComputationPath Cfg)
    (h_start : γ.distAt 0 = barrier.inputDist)
    (h_end : γ.distAt γ.numSteps = barrier.outputDist)
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (hΔ_bound : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ Δ)
    (hΔ_compat : Δ ≤ barrier.maxStepSize) :
    (γ.numSteps : ℝ) ≥
    Real.exp (barrier.growthRate * (barrier.problemSize : ℝ)) / Δ :=
  (barrier.toSeparationPrinciple γ h_start h_end Δ hΔ_pos
    hΔ_bound hΔ_compat).step_lower_bound

/-- **The exponential step count lower bound (Nat form).**

If the number of steps is at most `T`, then `T` must satisfy
the exponential bound.  Useful for contradiction arguments. -/
theorem PhaseTransitionBarrier.steps_exponential
    (barrier : PhaseTransitionBarrier Cfg)
    (γ : ComputationPath Cfg)
    (h_start : γ.distAt 0 = barrier.inputDist)
    (h_end : γ.distAt γ.numSteps = barrier.outputDist)
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (hΔ_bound : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ Δ)
    (hΔ_compat : Δ ≤ barrier.maxStepSize)
    (B : ℝ)
    (hB : Real.exp (barrier.growthRate *
      (barrier.problemSize : ℝ)) / Δ ≥ B) :
    (γ.numSteps : ℝ) ≥ B :=
  le_trans hB (barrier.step_lower_bound γ h_start h_end
    Δ hΔ_pos hΔ_bound hΔ_compat)

end Assembly

/-! ## Part 4: The Curvature Origin (Axiomatised)

This section provides the **physical explanation** for why the
restricted path barrier exists: Fisher curvature divergence at
the phase transition creates a bottleneck that locally-constrained
paths cannot shortcut.

The key insight (corrected): the curvature divergence does NOT
make the endpoint distance exponential (that's bounded by π).
Instead, it makes the *restricted path length* exponential by
creating a bottleneck where:

1. The Fisher metric is exponentially stiff in the direction
   across the transition.
2. Locally-constrained moves (TM pushforwards) can only move
   in directions nearly orthogonal to the geodesic.
3. The path must therefore wind through the high-curvature
   region, accumulating exponential total length.

This is analogous to a mountain pass: the straight-line distance
across the ridge is short, but if you can only take small steps
and the terrain is steep, you're forced to switchback, making
the actual hiking distance much longer.
-/

section Curvature

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- A **one-parameter family** of distributions on a finite type,
parameterised by a control parameter `α : ℝ`.

For SAT: `α` is the clause-to-variable ratio, and `family α`
is the distribution over configurations induced by a random
formula drawn at ratio α. -/
structure OneParamFamily (Cfg : Type*) [Fintype Cfg]
    [DecidableEq Cfg] where
  /-- The family: α ↦ distribution. -/
  family : ℝ → FinDist Cfg
  /-- The input value of the control parameter. -/
  α_in : ℝ
  /-- The output value of the control parameter. -/
  α_out : ℝ
  /-- The critical value (phase transition point). -/
  α_c : ℝ
  /-- Ordering: input < critical < output. -/
  h_order_in : α_in < α_c
  h_order_out : α_c < α_out

/-- The **curvature origin** of a phase transition barrier.

Axiomatises the chain:

1. Fisher information diverges at α_c with rate ≥ `exp(cn)`.
2. This divergence creates a bottleneck for locally-constrained
   paths crossing from α_in to α_out.
3. The minimum thermodynamic length of any such path is
   at least `exp(c' · n)`.

**Important correction:** The old formulation asserted that
the Fisher–Rao *endpoint distance* was exponential.  This was
wrong: `d_FR ≤ π` on any finite simplex.  The corrected
formulation asserts that the *restricted path length* (minimum
over paths with bounded per-step displacement) is exponential.

The geodesic may be short, but the Turing machine can't take
it.  The curvature bottleneck forces locally-constrained paths
to be exponentially longer than the geodesic.

**Axiom fields (Approach A):**

- `fisherInfo`: The scalar Fisher information along the family.
- `info_diverges`: `I(α_c) ≥ exp(c · n)` (curvature divergence).
- `restricted_path_bound`: Any locally-constrained path through
  the transition has length ≥ `exp(c' · n)`.

**Discharge route (Approach B):**

- `info_diverges`: From finite-size scaling of the k-SAT
  partition function and the susceptibility–Fisher identity.
- `restricted_path_bound`: From showing that near α_c, the
  TM-achievable directions are orthogonal to the geodesic
  direction, with the orthogonality quantified by the
  divergent Fisher information. -/
structure CurvatureOrigin
    (Cfg : Type*) [Fintype Cfg] [DecidableEq Cfg] extends
    OneParamFamily Cfg where
  /-- Problem size. -/
  problemSize : ℕ
  /-- The scalar Fisher information along the family. -/
  fisherInfo : ℝ → ℝ
  /-- Fisher information is nonneg. -/
  fisherInfo_nonneg : ∀ α, 0 ≤ fisherInfo α
  /-- Growth rate for the curvature divergence. -/
  growthRate : ℝ
  growthRate_pos : 0 < growthRate
  /-- **Axiom (Curvature divergence).**
  The Fisher information at the critical point diverges
  exponentially with problem size.

  `I(α_c) ≥ exp(c · n)` -/
  info_diverges :
    fisherInfo α_c ≥ Real.exp (growthRate * (problemSize : ℝ))
  /-- The maximum per-step displacement for which the
  bottleneck effect applies. -/
  maxStepSize : ℝ
  maxStepSize_pos : 0 < maxStepSize
  /-- Effective growth rate for the restricted path bound.
  May differ from `growthRate` (e.g. c' ≈ c/2 due to the
  square root in the length functional).  Still exponential. -/
  effectiveRate : ℝ
  effectiveRate_pos : 0 < effectiveRate
  /-- **Axiom (Restricted path length bound).**

  Any path from `family(α_in)` to `family(α_out)` with
  per-step displacement ≤ `maxStepSize` has thermodynamic
  length ≥ `exp(c' · n)`.

  This replaces the old (incorrect) endpoint distance bound.
  The geodesic may be short (≤ π), but locally-constrained
  paths are forced through the curvature bottleneck and
  must be exponentially long. -/
  restricted_path_bound :
    ∀ (γ : ComputationPath Cfg),
      γ.distAt 0 = family α_in →
      γ.distAt γ.numSteps = family α_out →
      (∀ t, t < γ.numSteps →
        γ.stepDisplacement t ≤ maxStepSize) →
      γ.thermodynamicLength ≥
      Real.exp (effectiveRate * (problemSize : ℝ))

namespace CurvatureOrigin

variable (origin : CurvatureOrigin Cfg)

/-- Construct a `PhaseTransitionBarrier` from a `CurvatureOrigin`.

The barrier's input/output distributions are the family evaluated
at α_in and α_out.  The growth rate is the effective rate.
The `maxStepSize` is inherited from the curvature origin.

**This is not an axiom — it is a definition.** The barrier's
`restricted_length_exponential` field is directly supplied by
the curvature origin's `restricted_path_bound`. -/
def toBarrier : PhaseTransitionBarrier Cfg where
  problemSize := origin.problemSize
  inputDist := origin.family origin.α_in
  outputDist := origin.family origin.α_out
  growthRate := origin.effectiveRate
  growthRate_pos := origin.effectiveRate_pos
  maxStepSize := origin.maxStepSize
  maxStepSize_pos := origin.maxStepSize_pos
  restricted_length_exponential := origin.restricted_path_bound

/-- The barrier inherits the exponential length lower bound. -/
theorem length_lower_bound
    (γ : ComputationPath Cfg)
    (h_start : γ.distAt 0 = origin.family origin.α_in)
    (h_end : γ.distAt γ.numSteps = origin.family origin.α_out)
    (h_steps : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ origin.maxStepSize) :
    γ.thermodynamicLength ≥
    Real.exp (origin.effectiveRate * (origin.problemSize : ℝ)) :=
  origin.toBarrier.length_lower_bound γ h_start h_end h_steps

/-- The barrier inherits the exponential step lower bound. -/
theorem step_lower_bound
    (γ : ComputationPath Cfg)
    (h_start : γ.distAt 0 = origin.family origin.α_in)
    (h_end : γ.distAt γ.numSteps = origin.family origin.α_out)
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (hΔ_bound : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ Δ)
    (hΔ_compat : Δ ≤ origin.maxStepSize) :
    (γ.numSteps : ℝ) ≥
    Real.exp (origin.effectiveRate * (origin.problemSize : ℝ)) / Δ :=
  origin.toBarrier.step_lower_bound γ h_start h_end
    Δ hΔ_pos hΔ_bound hΔ_compat

end CurvatureOrigin

end Curvature

/-! ## Part 5: The SAT Phase Transition

The random k-SAT problem at clause-to-variable ratio
`α = α_c ≈ 4.267` (for k = 3) undergoes a sharp phase
transition where the solution space shatters.

The shattering creates a bottleneck for locally-constrained
paths through distribution space.  Any algorithm that
determines satisfiability — implemented as a sequence of
local pushforwards — must traverse this bottleneck, requiring
exponential total thermodynamic length.
-/

section SAT

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- A **SAT barrier** for a specific problem size `n` and
configuration space `Cfg`.

Bundles a `PhaseTransitionBarrier` with the assertion that the
barrier's input and output distributions correspond to the
"unsolved" and "solved" states of a SAT computation.

**Axiom fields (Approach A):**

- `barrier`: The `PhaseTransitionBarrier` (restricted path length).
- `solver_endpoints`: Any correct SAT solver, when run on the
  appropriate input distribution, starts at `inputDist` and ends
  at `outputDist`. -/
structure SATBarrier
    (Cfg : Type*) [Fintype Cfg] [DecidableEq Cfg] where
  /-- The underlying phase transition barrier. -/
  barrier : PhaseTransitionBarrier Cfg
  /-- **Axiom (Input encodes unsolved).**
  Placeholder — the actual condition would reference a SAT
  encoding function. -/
  h_input_unsolved : True
  /-- **Axiom (Output encodes solved).** Placeholder. -/
  h_output_solved : True
  /-- **Axiom (Solver endpoints).**
  Any computation that correctly solves SAT on the random
  distribution at α_c must start at the input distribution
  and end at the output distribution. -/
  solver_endpoints :
    ∀ (γ : ComputationPath Cfg),
      γ.initDist = barrier.inputDist →
      γ.distAt γ.numSteps = barrier.outputDist

namespace SATBarrier

variable (sat : SATBarrier Cfg)

/-- **The exponential lower bound for SAT.**

Any correct SAT solver with per-step displacement bounded by
`Δ ≤ barrier.maxStepSize` requires at least `exp(c·n) / Δ` steps.

  `T ≥ exp(c · n) / Δ` -/
theorem exponential_sat_steps
    (γ : ComputationPath Cfg)
    (h_init : γ.initDist = sat.barrier.inputDist)
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (hΔ_bound : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ Δ)
    (hΔ_compat : Δ ≤ sat.barrier.maxStepSize) :
    (γ.numSteps : ℝ) ≥
    Real.exp (sat.barrier.growthRate *
      (sat.barrier.problemSize : ℝ)) / Δ := by
  have h_start : γ.distAt 0 = sat.barrier.inputDist := by
    simp [ComputationPath.distAt, h_init]
  have h_end := sat.solver_endpoints γ h_init
  exact sat.barrier.step_lower_bound γ h_start h_end
    Δ hΔ_pos hΔ_bound hΔ_compat

/-- **Contradiction form:** a polynomial-time SAT solver implies
the number of steps is simultaneously polynomial (by assumption)
and exponential (by the barrier), which is impossible for large n.

Given:
- A SAT solver running in `T` steps
- Per-step displacement `≤ Δ ≤ barrier.maxStepSize`
- `T · Δ < exp(c · n)` (polynomial resources below exponential)

Derives: `False`. -/
theorem poly_time_contradicts_barrier
    (γ : ComputationPath Cfg)
    (h_init : γ.initDist = sat.barrier.inputDist)
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (hΔ_bound : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ Δ)
    (hΔ_compat : Δ ≤ sat.barrier.maxStepSize)
    (h_poly : (γ.numSteps : ℝ) * Δ <
      Real.exp (sat.barrier.growthRate *
        (sat.barrier.problemSize : ℝ))) :
    False := by
  have h_steps := sat.exponential_sat_steps γ h_init
    Δ hΔ_pos hΔ_bound hΔ_compat
  have h_mul : (γ.numSteps : ℝ) * Δ ≥
      Real.exp (sat.barrier.growthRate *
        (sat.barrier.problemSize : ℝ)) := by
    rwa [ge_iff_le, div_le_iff₀ hΔ_pos] at h_steps
  linarith

end SATBarrier

end SAT

/-! ## Part 6: The Curie–Weiss Proof of Concept

The Curie–Weiss model validates the *method* (curvature
divergence → restricted path length lower bound) while
correctly predicting that mean-field problems are easy
(polynomial barrier, not exponential).

For Curie–Weiss with `n` spins:
- Fisher information at β_c: `I(β_c) ~ n^{4/3}`
- Restricted path length through the transition: `~ n^{2/3}`

This is polynomial — correctly reflecting that mean-field
models lack the clustering needed for exponential hardness.
-/

section CurieWeiss

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- A **Curie–Weiss barrier** (proof of concept).

Demonstrates the `CurvatureOrigin → PhaseTransitionBarrier`
pipeline on a model where the barrier is polynomial.  This
correctly reflects the physics: mean-field problems are
computationally easy.

**Axiom fields** encode the known exact results for the
Curie–Weiss Fisher information and restricted path length. -/
structure CurieWeissBarrier
    (Cfg : Type*) [Fintype Cfg] [DecidableEq Cfg] where
  /-- Problem size (number of spins). -/
  n : ℕ
  /-- The one-parameter family (β ↦ Gibbs distribution). -/
  family : ℝ → FinDist Cfg
  /-- Critical inverse temperature. -/
  β_c : ℝ
  /-- Sub-critical value. -/
  β_in : ℝ
  h_in : β_in < β_c
  /-- Super-critical value. -/
  β_out : ℝ
  h_out : β_c < β_out
  /-- Fisher information at the critical point.
  For Curie–Weiss: `I(β_c) ~ n^{4/3}`. -/
  fisherInfo_critical : ℝ
  h_info_scaling : fisherInfo_critical ≥ (n : ℝ) ^ (4/3 : ℝ)
  /-- Maximum step size for the restricted path bound. -/
  maxStepSize : ℝ
  maxStepSize_pos : 0 < maxStepSize
  /-- Restricted path length through the transition.
  For Curie–Weiss: paths with step size ≤ maxStepSize have
  length ≥ `n^{2/3}` (polynomial). -/
  h_restricted_length :
    ∀ (γ : ComputationPath Cfg),
      γ.distAt 0 = family β_in →
      γ.distAt γ.numSteps = family β_out →
      (∀ t, t < γ.numSteps →
        γ.stepDisplacement t ≤ maxStepSize) →
      γ.thermodynamicLength ≥ (n : ℝ) ^ (2/3 : ℝ)

/-- The Curie–Weiss barrier produces a `PhaseTransitionBarrier`
with **polynomial** (not exponential) growth.

This correctly reflects the physics: mean-field problems are
computationally easy. -/
def CurieWeissBarrier.toBarrier (cw : CurieWeissBarrier Cfg)
    (hc : (0:ℝ) < Real.log ((cw.n : ℝ) ^ (2/3 : ℝ)))
    (hn : (1 : ℝ) ≤ (cw.n : ℝ)) :
    PhaseTransitionBarrier Cfg where
  problemSize := cw.n
  inputDist := cw.family cw.β_in
  outputDist := cw.family cw.β_out
  growthRate := Real.log ((cw.n : ℝ) ^ (2/3 : ℝ)) / (cw.n : ℝ)
  growthRate_pos := by positivity
  maxStepSize := cw.maxStepSize
  maxStepSize_pos := cw.maxStepSize_pos
  restricted_length_exponential := by
    intro γ h_start h_end h_steps
    -- exp(log(n^{2/3})/n · n) = exp(log(n^{2/3})) = n^{2/3}
    rw [div_mul_cancel₀]
    · rw [Real.exp_log (by positivity : (0:ℝ) < (cw.n : ℝ) ^ (2/3 : ℝ))]
      exact cw.h_restricted_length γ h_start h_end h_steps
    · linarith

end CurieWeiss

/-! ## Summary: What This File Establishes

### The restricted path length barrier (CORRECTED)

**Key correction:** The Fisher–Rao distance on a finite simplex
is bounded by π.  Endpoint distance CANNOT be exponential.
The barrier is now about *restricted path length*: paths whose
per-step displacement is bounded (as Turing machine paths are)
must have exponential total length to cross the phase transition.

1. **`PhaseTransitionBarrier` (Axiomatised):**
   Any locally-constrained path from input to output has
   exponential thermodynamic length: `𝓛[γ] ≥ exp(c·n)`.

2. **`length_lower_bound` (Proved):**
   Direct consequence of the barrier axiom.

3. **`toSeparationPrinciple` (Proved):**
   Barrier + locality → `SeparationPrinciple`: `T ≥ exp(c·n) / Δ`.
   Requires `Δ ≤ maxStepSize` for compatibility.

4. **`step_lower_bound` (Proved):**
   Exponential step count: `T ≥ exp(c·n) / Δ`.

### The curvature origin

5. **`CurvatureOrigin` (Axiomatised):**
   One-parameter family with Fisher information divergence at
   α_c and exponential restricted path length.

6. **`CurvatureOrigin.toBarrier` (Proved):**
   Curvature divergence → PhaseTransitionBarrier.

### The SAT application

7. **`SATBarrier` (Axiomatised):**
   The random k-SAT transition satisfies the barrier axioms.

8. **`exponential_sat_steps` (Proved):**
   `T ≥ exp(c·n) / Δ` for any correct SAT solver.

9. **`poly_time_contradicts_barrier` (Proved):**
   A polynomial-time solver contradicts the exponential barrier.

### The axiom manifest (CORRECTED)

| # | Axiom | Structure | Physical Content |
|---|-------|-----------|-----------------|
| 1 | Restricted path length | `PhaseTransitionBarrier` | 𝓛 ≥ exp(cn) for locally-constrained paths |
| 2 | Fisher info divergence | `CurvatureOrigin` | I(α_c) ≥ exp(cn) (curvature singularity) |
| 3 | Restricted path bound | `CurvatureOrigin` | 𝓛 ≥ exp(c'n) through bottleneck |
| 4 | Solver endpoints | `SATBarrier` | SAT solver goes inputDist → outputDist |
| 5 | TM locality | `TMTransition` | d_FR(p, f_*p) ≤ Δ for all p |
| 6 | Chentsov invariance | `ChentsovAxioms` | Fisher–Rao preserved under sufficient stats |
| 7 | Chentsov uniqueness | `ChentsovAxioms` | Fisher–Rao is the unique such metric |

### What changed from v1

The old Axiom 1 (`distance_exponential`) asserted
`d_FR(input, output) ≥ exp(cn)`.  This is **unsatisfiable**:
`d_FR ≤ π` always.  Combining the old axiom with
`fisherRao_le_pi` would derive `False` directly — the old
axiom system was inconsistent on purely geometric grounds.

The new Axiom 1 (`restricted_length_exponential`) asserts that
*locally-constrained paths* have exponential length.  This is
satisfiable: a path can have arbitrarily large thermodynamic
length even between points that are close in geodesic distance.
The path winds through the high-curvature region because the
TM's allowed moves don't align with the geodesic.

The physical content is the same (curvature divergence at the
phase transition creates an information-geometric barrier).
The mathematical formulation is corrected.
-/

end
