/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/Defs.lean
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic
/-!
# The Sewing Lemma — Layer 1 (Interval-Length Control)

The **Sewing Lemma** constructs additive functionals from almost-additive approximations.
This file proves the simplest and most directly useful version: the defect of the
two-parameter map `Ξ` is controlled by `K · |t - s|^θ` with `θ > 1`.

## Why this version?

The interval length `|t - s|` distributes *perfectly* over dyadic subdivision: at level `n`,
each sub-interval has length exactly `|t - s| / 2ⁿ`. This gives clean geometric decay:

  `‖S_{n+1} - Sₙ‖ ≤ K · |t - s|^θ · 2^{-n(θ - 1)}`

with *no additional hypotheses* on a control function. The general sewing lemma with
abstract super-additive control `ω` requires either a Lipschitz condition on `ω` or
a fundamentally different (compactness-based) proof. This version avoids both issues.

## Coverage

This version handles all standard applications where the driving signal has Hölder regularity:
* Standard Brownian motion (`γ`-Hölder for `γ < 1/2`)
* Fractional Brownian motion (`γ`-Hölder for `γ < H`)
* Hölder-regular Young integration
* Rough integration with Hölder rough path data

For the cross-controlled version with two different controls `ω₁, ω₂` (needed when the
integrand and integrator have different regularity structures), see Layer 2.

## Main results

* `dyadicSum_diff_bound₁`: geometric decay of successive dyadic refinements
* `dyadicSum_cauchy₁`: the dyadic Riemann sums form a Cauchy sequence
* `sewingMap₁_dist_le`: approximation bound `‖I(s,t) - Ξ(s,t)‖ ≤ C·K·|t-s|^θ`
* `sewingMap₁_additive`: the sewn map is genuinely additive
* `sewingMap₁_unique`: uniqueness among additive functionals with the approximation bound

## References

* [Gubinelli, M., *Controlling rough paths*][gubinelli2004]
* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Theorem 2.2][friz2020]
* [Lyons, T., *Differential equations driven by rough signals*][lyons1998]
-/
noncomputable section

open Real --NNReal

open Set Filter

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

section Defect₁

/-- The defect of `Ξ` at `(s, u, t)`: measures failure of additivity.
`δΞ(s, u, t) = Ξ(s, t) - Ξ(s, u) - Ξ(u, t)`. -/
def sewingDefect₁ (Ξ : ℝ → ℝ → E) (s u t : ℝ) : E :=
  Ξ s t - Ξ s u - Ξ u t

end Defect₁

/-! ### The Sewing Condition (Layer 1) -/

/-- **Sewing Condition, Layer 1**: the defect of `Ξ` is controlled by interval length.

This is the simplest version: `‖δΞ(s, u, t)‖ ≤ K · |t - s|^θ` with `θ > 1`.

The exponent condition `θ > 1` is sharp. For `θ = 1`, the dyadic refinement sums diverge
logarithmically (think of the harmonic series). For `θ < 1` they diverge polynomially.
The condition `θ > 1` is precisely what makes the geometric series `∑ 2^{-n(θ-1)}` converge.

In the rough paths literature:
  * Young integration has `θ = 1/p + 1/q > 1` (when both paths are Hölder)
  * Rough integration (level 2) has `θ = 3/p > 1` for `p < 3`
  * Rough integration (level N) has `θ = (N+1)/p > 1` for `p < N + 1` -/
structure SewingCondition₁ (Ξ : ℝ → ℝ → E) (θ K : ℝ) (a b : ℝ) : Prop where
  /-- `Ξ` vanishes on the diagonal: `Ξ(s, s) = 0`. -/
  vanish_diag : ∀ s, Ξ s s = 0
  /-- The exponent is strictly greater than 1. -/
  one_lt_theta : 1 < θ
  /-- The bound constant is nonneg. -/
  K_nonneg : 0 ≤ K
  /-- The interval is well-oriented. -/
  hab : a ≤ b
  /-- The defect bound: `‖δΞ(s, u, t)‖ ≤ K · |t - s|^θ`. -/
  defect_bound : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ‖sewingDefect₁ Ξ s u t‖ ≤ K * |t - s| ^ θ

/-! ### The Sewing Condition (Layer 2) -/

/-- **Sewing Condition, Layer 2**: the defect is controlled by a *product* of two
Lipschitz controls.

`‖δΞ(s, u, t)‖ ≤ K · ω₁(s, u)^α · ω₂(u, t)^β`

with `α + β > 1` and each `ωᵢ` Lipschitz in interval length.

The product structure is not a mere generalization — it's the *natural* form of the
defect in integration theory. When you write `Ξ(s,t) = Y(s) · (X(t) - X(s))`, the
defect `δΞ(s,u,t) = -(Y(u) - Y(s)) · (X(t) - X(u))` separates into a factor
depending on `[s, u]` (the integrand's variation) and a factor depending on `[u, t]`
(the integrator's variation). -/
structure SewingCondition₂ (Ξ : ℝ → ℝ → E)
    (ω₁ ω₂ : ℝ → ℝ → ℝ) (α β K L₁ L₂ : ℝ) (a b : ℝ) : Prop where
  vanish_diag : ∀ s, Ξ s s = 0
  one_lt_exp : 1 < α + β
  α_nonneg : 0 ≤ α
  β_nonneg : 0 ≤ β
  K_nonneg : 0 ≤ K
  hab : a ≤ b
  ω₁_nonneg : ∀ s t, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ω₁ s t
  ω₁_diag : ∀ s, ω₁ s s = 0
  ω₁_superadd : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ω₁ s u + ω₁ u t ≤ ω₁ s t
  ω₁_lip : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ω₁ s t ≤ L₁ * (t - s)
  defect_bound : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ‖sewingDefect₁ Ξ s u t‖ ≤ K * ω₁ s u ^ α * ω₂ u t ^ β
  L₁_nonneg : 0 ≤ L₁
  L₂_nonneg : 0 ≤ L₂
  ω₂_nonneg : ∀ s t, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ω₂ s t
  ω₂_lip : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ω₂ s t ≤ L₂ * (t - s)

/-! ### Dyadic partition points -/

section Dyadic

/-- The `k`-th point of the `n`-th dyadic partition of `[s, t]`. -/
def dyadicPt (s t : ℝ) (n k : ℕ) : ℝ :=
  s + ↑k * (t - s) / (2 : ℝ) ^ (n : ℕ)

end Dyadic

/-! ### Dyadic Riemann sums -/

section DyadicSums₁

/-- The `n`-th dyadic Riemann sum of `Ξ` over `[s, t]`. -/
def dyadicSum₁ (Ξ : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) : E :=
  ∑ k ∈ Finset.range (2 ^ n),
    Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1))

end DyadicSums₁

/-! ### Cauchy sequence and convergence -/

section Convergence₁

/-- The geometric ratio for the Cauchy bound. -/
def sewingRatio₁ (θ : ℝ) : ℝ := (2 : ℝ)⁻¹ ^ (θ - 1)

/-- The geometric ratio for Layer 2: `r₂(α, β) = 2^{-(α+β-1)}`. -/
def sewingRatio₂ (α β : ℝ) : ℝ := (2 : ℝ)⁻¹ ^ (α + β - 1)


/- The geometric constant -/
def sewingConst₁ (θ : ℝ) : ℝ := 1 / (1 - sewingRatio₁ θ)

/-- The sewing constant for Layer 2. -/
def sewingConst₂ (α β : ℝ) : ℝ := 1 / (1 - sewingRatio₂ α β)

end Convergence₁

section SewnMap

/-- **The sewn map**: the limit of dyadic Riemann sums.
`I(s, t) = lim_{n→∞} Sₙ(s, t)` -/
def sewingMap₁ (Ξ : ℝ → ℝ → E) [CompleteSpace E] (θ K a b : ℝ)
    (_hΞ : SewingCondition₁ Ξ θ K a b) (s t : ℝ) : E :=
  if _h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    limUnder atTop (fun n => dyadicSum₁ Ξ s t n)
  else
    0

/-- **The sewn map (Layer 2)**: same construction, different hypotheses. -/
def sewingMap₂ (Ξ : ℝ → ℝ → E) [CompleteSpace E]
    (ω₁ ω₂ : ℝ → ℝ → ℝ) (α β K L₁ L₂ a b : ℝ)
    (_hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b) (s t : ℝ) : E :=
  if _h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    limUnder atTop (fun n => dyadicSum₁ Ξ s t n)
  else
    0

end SewnMap

section Lipschitz
/-! ### Lipschitz controls -/

/-- A **Lipschitz control** on `[a, b]`: a function `ω : ℝ → ℝ → ℝ` that is
nonneg, vanishes on the diagonal, is super-additive, and grows at most linearly
in the interval length.

The Lipschitz condition `ω(s, t) ≤ L · (t - s)` is the key regularity that makes
the dyadic proof work: it ensures `ω(t_k, t_{k+1}) ≤ L · |t-s| / 2^n` at level `n`.

**Examples**:
* `ω(s,t) = |t - s|` with `L = 1` (Layer 1 control)
* `ω(s,t) = ‖X‖_{p-var;[s,t]}^p` for a `γ`-Hölder `X`, with `L = C^p · |b-a|^{γp - 1}`
* `ω(s,t) = |f(t) - f(s)|^p` for Lipschitz `f`, with `L = (Lip f)^p · |b-a|^{p-1}` -/
structure LipControl (ω : ℝ → ℝ → ℝ) (a b : ℝ) where
  nonneg : ∀ s t, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ω s t
  /-- The control vanishes on the diagonal. -/
  diag : ∀ s, ω s s = 0
  /-- The control is super-additive on `[a, b]`. -/
  superadd : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ω s u + ω u t ≤ ω s t
  /-- The Lipschitz-in-length bound. -/
  lip_const : ℝ
  /-- The Lipschitz constant is nonneg. -/
  lip_const_nonneg : 0 ≤ lip_const
  /-- The Lipschitz bound: `ω(s, t) ≤ L · (t - s)`. -/
  lip_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ω s t ≤ lip_const * (t - s)

end Lipschitz

/-! ### Layer 1 as a special case of Layer 2 -/

section Specialization

/-- The interval-length function `|t - s|` is a Lipschitz control with constant 1. -/
def lipControl_abs_sub {a b : ℝ} (_hab : a ≤ b) :
    LipControl (fun s t => |t - s|) a b where
  nonneg := fun s t _ _ _ => abs_nonneg _
  diag := fun s => by simp
  superadd := fun s u t _ hsu hut _ => by
    rw [show t - s = (u - s) + (t - u) from by ring]
    rw [@le_abs']
    simp only [sub_add_sub_cancel', neg_add_rev, le_add_neg_iff_add_le]
    grind only [= abs.eq_1, = max_def]
  lip_const := 1
  lip_const_nonneg := zero_le_one' ℝ
  lip_bound := fun s t _ hst _ => by
    simp [abs_of_nonneg (sub_nonneg.mpr hst)]

/-! ### Continuous controls -/

section ContinuousControl

/-- A **continuous control** on `[a, b]`: a super-additive function vanishing on the
diagonal, with continuity near the diagonal.

The continuity condition can be stated as: `ω(s, t) → 0` as `t - s → 0`,
uniformly for `s, t ∈ [a, b]`. This is equivalent to `ω` being continuous at
every point `(s, s)` on the diagonal, which in turn follows from `ω` being
continuous as a function `ℝ × ℝ → ℝ`. -/
structure ContinuousControl (ω : ℝ → ℝ → ℝ) (a b : ℝ) extends LipControl ω a b where
  -- We DROP the Lipschitz condition and replace it with continuity.
  -- (LipControl is reused only for the shared fields; we override lip_bound.)
  /-- Continuity near the diagonal: for all `ε > 0`, there exists `δ > 0` such that
  `ω(s, t) < ε` whenever `s, t ∈ [a, b]` and `|t - s| < δ`. -/
  cont_diag : ∀ ε > 0, ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    t - s < δ → ω s t < ε

-- NOTE: In retrospect, we should NOT extend LipControl here, since we don't
-- have the Lipschitz bound. Instead, extract the common fields into a base
-- structure. For now, we define ContinuousControl from scratch:

/-- A continuous super-additive control (standalone, not extending LipControl). -/
structure ContControl (ω : ℝ → ℝ → ℝ) (a b : ℝ) : Prop where
  /-- Nonnegativity. -/
  nonneg : ∀ s t, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ω s t
  /-- Vanishes on diagonal. -/
  diag : ∀ s, ω s s = 0
  /-- Super-additivity. -/
  superadd : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ω s u + ω u t ≤ ω s t
  /-- Continuity near the diagonal (uniform on `[a, b]`). -/
  cont_diag : ∀ ε > 0, ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    t - s < δ → ω s t < ε

end ContinuousControl
end Specialization
section Partion
/-- A **partition** of a real interval: a monotone sequence of `n + 1` points
`t₀ ≤ t₁ ≤ ⋯ ≤ tₙ` with `t₀ = s` and `tₙ = t`.

We use `Fin (n + 1)` indexing for clean boundary access. -/
structure Partition (s t : ℝ) where
  /-- Number of sub-intervals. -/
  n : ℕ
  /-- The partition points. -/
  pts : Fin (n + 1) → ℝ
  /-- The partition is monotone. -/
  mono : Monotone pts
  /-- The first point is `s`. -/
  first : pts ⟨0, Nat.zero_lt_succ n⟩ = s
  /-- The last point is `t`. -/
  last : pts ⟨n, Nat.lt_succ_of_le le_rfl⟩ = t

/-- The `i`-th sub-interval endpoint, for `i ≤ n`. -/
def Partition.point {s t : ℝ} (P : Partition s t) (i : Fin (P.n + 1)) : ℝ :=
  P.pts i

/-- The left endpoint of the `i`-th sub-interval (for `i < n`). -/
def Partition.left {s t : ℝ} (P : Partition s t) (i : Fin P.n) : ℝ :=
  P.pts ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- The right endpoint of the `i`-th sub-interval. -/
def Partition.right {s t : ℝ} (P : Partition s t) (i : Fin P.n) : ℝ :=
  P.pts ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- The mesh of a partition: the maximum sub-interval length. -/
def Partition.mesh {s t : ℝ} (P : Partition s t) : ℝ :=
  if h : P.n = 0 then 0
  else Finset.sup' (Finset.univ (α := Fin P.n))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩)
    (fun i => P.right i - P.left i)

/-- The trivial partition: one interval `[s, t]`. -/
def Partition.trivial (s t : ℝ) (hst : s ≤ t) : Partition s t where
  n := 1
  pts := ![s, t]
  mono := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    interval_cases i <;> interval_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  first := by simp [Matrix.cons_val_zero]
  last := by simp [Matrix.cons_val_one]

/-- **Refinement**: partition `P'` refines `P` if every point of `P` appears in `P'`. -/
def Partition.IsRefinement {s t : ℝ} (P' P : Partition s t) : Prop :=
  ∀ i : Fin (P.n + 1), ∃ j : Fin (P'.n + 1), P'.pts j = P.pts i

/-- **The Riemann sum** of a two-parameter map `Ξ` over a partition `P`:
`RS(P) = ∑ᵢ Ξ(tᵢ, tᵢ₊₁)`. -/
def riemannSum (Ξ : ℝ → ℝ → E) {s t : ℝ} (P : Partition s t) : E :=
  ∑ i : Fin P.n, Ξ (P.left i) (P.right i)

end Partion

/-- The **θ-energy** of a partition with respect to control `ω`:
`Φ_θ(P) = ∑ᵢ ω(tᵢ, tᵢ₊₁)^θ`.

This is the fundamental quantity that controls error in the general sewing lemma.
It combines super-additivity (which bounds `∑ ω_i`) with the exponent `θ > 1`
(which penalises large individual terms). -/
def thetaEnergy (ω : ℝ → ℝ → ℝ) (θ : ℝ) {s t : ℝ} (P : Partition s t) : ℝ :=
  ∑ i : Fin P.n, ω (P.left i) (P.right i) ^ θ

/-! ### Dyadic partitions as `Partition` objects -/

@[simp]
theorem dyadicPt_zero (s t : ℝ) (n : ℕ) : dyadicPt s t n 0 = s := by
  simp [dyadicPt]

theorem dyadicPt_last (s t : ℝ) (n : ℕ) : dyadicPt s t n (2 ^ n) = t := by
  simp [dyadicPt]

/-- Monotonicity: dyadic points are ordered when `s ≤ t`. -/
theorem dyadicPt_mono {s t : ℝ} (hst : s ≤ t) (n : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    dyadicPt s t n j ≤ dyadicPt s t n k := by
  simp only [dyadicPt]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (n : ℕ) := by positivity
  gcongr
  linarith

/-- The dyadic partition of `[s, t]` at level `n`, packaged as a `Partition`. -/
def dyadicPartition (s t : ℝ) (hst : s ≤ t) (n : ℕ) : Partition s t where
  n := 2 ^ n
  pts := fun ⟨k, _⟩ => dyadicPt s t n k
  mono := fun ⟨_, _⟩ ⟨_, _⟩ hij => dyadicPt_mono hst n hij
  first := dyadicPt_zero s t n
  last := dyadicPt_last s t n

/-! ### The Sewing Condition (Layer 3) -/

/-- **Sewing Condition, Layer 3**: the general version with continuous control.

`‖δΞ(s, u, t)‖ ≤ K · ω(s, t)^θ` with `θ > 1` and `ω` a continuous super-additive
control.

This is the version stated in Friz–Hairer and used in the general theory of rough paths.
It makes no assumption about the relationship between `ω(s, t)` and `|t - s|` beyond
continuity at the diagonal. -/
structure SewingCondition₃ (Ξ : ℝ → ℝ → E)
    (ω : ℝ → ℝ → ℝ) (θ K : ℝ) (a b : ℝ) : Prop where
  /-- `Ξ` vanishes on the diagonal. -/
  vanish_diag : ∀ s, Ξ s s = 0
  /-- The exponent is strictly greater than 1. -/
  one_lt_theta : 1 < θ
  /-- The bound constant is nonneg. -/
  K_nonneg : 0 ≤ K
  /-- The interval is well-oriented. -/
  hab : a ≤ b
  /-- The control is continuous and super-additive. -/
  omega_cont : ContControl ω a b
  /-- The defect bound. -/
  defect_bound : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ‖sewingDefect₁ Ξ s u t‖ ≤ K * ω s t ^ θ
  /-- Sumability Enhancement -/
  energy_summable : ∀ s t, a ≤ s → (hst : s ≤ t) → t ≤ b →
    Summable (fun n => thetaEnergy ω θ (dyadicPartition s t hst n))
  /-- MEH!-/
  energy_vanish : ∀ ε > 0, ∃ δ > 0, ∀ s t, a ≤ s → (hst : s ≤ t) → t ≤ b →
    t - s < δ → ∑' n, thetaEnergy ω θ (dyadicPartition s t hst n) < ε
  /-- MEEEEEHHHH-/
  xi_cont : ∀ ε > 0, ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    t - s < δ → ‖Ξ s t‖ < ε

/-- **Existence of the sewn map**: Riemann sums over partitions with vanishing
theta-energy converge.

We construct the limit using any sequence of partitions `Pₙ` with
`thetaEnergy ω θ Pₙ → 0` (e.g., dyadic partitions, or uniform partitions with
mesh → 0). -/
def sewingMap₃ (Ξ : ℝ → ℝ → E) [CompleteSpace E]
    (ω : ℝ → ℝ → ℝ) (θ K a b : ℝ)
    (_hΞ : SewingCondition₃ Ξ ω θ K a b) (s t : ℝ) : E :=
  if _h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    -- Use dyadic partitions as the canonical approximating sequence.
    -- The limit exists because Riemann sums are Cauchy (by riemannSum_comparison
    -- + thetaEnergy_tendsto_zero).
    limUnder atTop (fun n => dyadicSum₁ Ξ s t n)
  else
    0

end StochCalc
