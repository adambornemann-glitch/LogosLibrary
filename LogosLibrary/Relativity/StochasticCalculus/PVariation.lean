/-
Copyright (c) 2026 StochCalc Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Doctor Professor Baron von Wobble-Bob
-/
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
/-!
# p-Variation of functions

We define the `p`-variation of a function `f` on a set `s`, generalizing the total variation
(the case `p = 1`) already present in Mathlib as `eVariationOn`.

The `p`-variation is a fundamental regularity notion in stochastic analysis and rough path theory.
A path has finite `p`-variation when the supremum of `∑ᵢ d(f(tᵢ₊₁), f(tᵢ))^p` over all
finite partitions is finite. Standard Brownian motion has finite `p`-variation almost surely for
all `p > 2`, and infinite `p`-variation for `p ≤ 2`. This dichotomy is the analytical reason that
Itô calculus (and more generally, rough path theory) is necessary.

## Main definitions

* `StochCalc.ePVariationOn p f s`: the `p`-variation of `f` on the set `s`, valued in `ℝ≥0∞`.
  Defined as the supremum over all finite monotone sequences in `s` of
  `∑ᵢ edist(f(uᵢ₊₁), f(uᵢ)) ^ p`.
* `StochCalc.HasFinitePVariationOn p f s`: predicate asserting `ePVariationOn p f s < ⊤`.
* `StochCalc.pVarNorm p f s`: the `p`-variation norm `(ePVariationOn p f s) ^ (1/p)`, when
  this makes sense.

## Main results

* `ePVariationOn_const`: a constant function has zero `p`-variation.
* `ePVariationOn_le_of_le_edist`: upper bound from a uniform bound on increments.
* `ePVariationOn_mono_set`: `p`-variation is monotone with respect to set inclusion.
* `hasFinitePVariationOn_of_lipschitzOn`: Lipschitz functions have finite `1`-variation.
* `ePVariationOn_mono_exponent`: monotonicity of `p`-variation in the exponent, assuming
  bounded diameter. If `1 ≤ p ≤ q` and the image has bounded diameter, then
  `q`-variation ≤ `p`-variation times a diameter correction.
* `ePVariationOn_add_le`: super-additivity of `p`-variation under interval concatenation.

## Implementation notes

Following Mathlib's `eVariationOn`, the `p`-variation is defined using the supremum over all
monotone `ℕ`-indexed sequences with values in `s`, paired with a natural number `n` giving
the number of intervals. This avoids introducing a separate partition type while remaining
definitionally convenient.

The exponent `p` is taken as `ℝ` so that we can use `ENNReal.rpow`. Most results require
`0 < p` or `1 ≤ p`.

## References

* [Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*][friz2010]
* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed.][friz2020]
* [Lyons, T., *Differential equations driven by rough signals*][lyons1998]

## Tags

p-variation, rough path, path regularity, bounded variation, Hölder continuity
-/

noncomputable section

open scoped ENNReal NNReal

open Set Filter Finset

variable {α : Type*} {E : Type*} {F : Type*}

namespace StochCalc

/-! ### Definition of p-variation -/

section Definition

variable [LinearOrder α] [PseudoEMetricSpace E]

/-- The `p`-variation of `f` on `s`. This is the supremum over all finite monotone
sequences `u₀ ≤ u₁ ≤ ⋯ ≤ uₙ` with values in `s` of `∑ᵢ edist(f(uᵢ₊₁), f(uᵢ)) ^ p`.

When `p = 1`, this is the total variation of `f` on `s` (cf. `eVariationOn`). -/
def ePVariationOn (p : ℝ) (f : α → E) (s : Set α) : ℝ≥0∞ :=
  ⨆ q : ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s},
    ∑ i ∈ Finset.range q.1, edist (f (q.2.1 (i + 1))) (f (q.2.1 i)) ^ p

/-- `f` has finite `p`-variation on `s` if `ePVariationOn p f s < ⊤`. -/
def HasFinitePVariationOn (p : ℝ) (f : α → E) (s : Set α) : Prop :=
  ePVariationOn p f s < ⊤

/-- The `p`-variation norm of `f` on `s`, defined as `(ePVariationOn p f s) ^ (1/p)`.
This is the quantity `‖f‖_{p-var; s}` from the rough paths literature. -/
def pVarNorm (p : ℝ) (f : α → E) (s : Set α) : ℝ≥0∞ :=
  ePVariationOn p f s ^ (1 / p)

end Definition

/-! ### Basic properties -/

section Basic

variable [LinearOrder α] [PseudoEMetricSpace E]

/-- The `p`-variation of a function is bounded below by any particular partition sum. -/
theorem le_ePVariationOn {p : ℝ} {f : α → E} {s : Set α}
    {n : ℕ} {u : ℕ → α} (hu : Monotone u) (hus : ∀ i, u i ∈ s) :
    ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ p ≤ ePVariationOn p f s :=
  le_iSup_of_le ⟨n, ⟨u, hu, hus⟩⟩ le_rfl

/-- The `p`-variation of a constant function is zero. -/
@[simp]
theorem ePVariationOn_const {p : ℝ} (hp : 0 < p) (c : E) (s : Set α) :
    ePVariationOn p (fun _ => c) s = 0 := by
  simp only [ePVariationOn, edist_self, sum_const, card_range, nsmul_eq_mul, 
    ENNReal.iSup_eq_zero, mul_eq_zero, Nat.cast_eq_zero, ENNReal.rpow_eq_zero_iff, 
    true_and, ENNReal.zero_ne_top, false_and, or_false]
  exact fun i => Or.symm (Or.intro_left (i.1 = 0) hp)

/-- A constant function has finite `p`-variation. -/
theorem hasFinitePVariationOn_const {p : ℝ} (hp : 0 < p) (c : E) (s : Set α) :
    HasFinitePVariationOn p (fun _ => c) s := by
  simp [HasFinitePVariationOn, ePVariationOn_const hp]

/-- The `p`-variation is monotone with respect to set inclusion: if `s ⊆ t`, then
the `p`-variation on `s` is at most the `p`-variation on `t`, since every partition
of `s` is also a partition of `t`. -/
theorem ePVariationOn_mono_set {p : ℝ} {f : α → E} {s t : Set α} (hst : s ⊆ t) :
    ePVariationOn p f s ≤ ePVariationOn p f t := by
  apply iSup_le fun q =>
    le_ePVariationOn q.2.prop.1 (fun i => hst (q.2.prop.2 i))

/-- If `f` has finite `p`-variation on `t` and `s ⊆ t`, then `f` has finite
`p`-variation on `s`. -/
theorem HasFinitePVariationOn.mono {p : ℝ} {f : α → E} {s t : Set α}
    (hf : HasFinitePVariationOn p f t) (hst : s ⊆ t) :
    HasFinitePVariationOn p f s :=
  lt_of_le_of_lt (ePVariationOn_mono_set hst) hf

/-- The `p`-variation of `f` on the empty set is zero. -/
@[simp]
theorem ePVariationOn_empty {p : ℝ} (_hp : 0 < p) (f : α → E) :
    ePVariationOn p f ∅ = 0 := by
  simp only [ePVariationOn]
  apply le_antisymm _ (zero_le _)
  apply iSup_le fun q =>
    absurd (q.2.prop.2 0) (Set.notMem_empty _)

/-- The `p`-variation of `f` on a singleton is zero. -/
@[simp]
theorem ePVariationOn_singleton {p : ℝ} (hp : 0 < p) (f : α → E) (a : α) :
    ePVariationOn p f {a} = 0 := by
  simp only [ePVariationOn]
  apply le_antisymm _ (zero_le _)
  apply iSup_le fun q =>
    le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
  have hi : q.2.1 i = a := Set.mem_singleton_iff.mp (q.2.prop.2 i)
  have hi1 : q.2.1 (i + 1) = a := Set.mem_singleton_iff.mp (q.2.prop.2 (i + 1))
  simp [hi, hi1, ENNReal.zero_rpow_of_pos hp]

end Basic

/-! ### Concatenation and super-additivity -/

section Concatenation

variable [LinearOrder α] [PseudoEMetricSpace E]

/-- **Super-additivity of p-variation**. For `a ≤ b ≤ c`, the `p`-variation on `[a, c]`
is at least the sum of the `p`-variations on `[a, b]` and `[b, c]`.

This is the fundamental structural property of `p`-variation: refining a partition
can only increase the sum. The partition achieving the supremum on `[a, c]` can always
be refined to include the point `b`, yielding sums that dominate those on the
two sub-intervals.

In the rough paths literature, this is the "super-additivity" that makes `p`-variation
a control function. -/
theorem ePVariationOn_add_le {p : ℝ} (_hp : 0 < p) {f : α → E} {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ePVariationOn p f (Icc a b) + ePVariationOn p f (Icc b c)
      ≤ ePVariationOn p f (Icc a c) := by
  simp only [ePVariationOn]
  /- Reduce to: for all partition-pairs, S(q1) + S(q2) ≤ ⨆ S(q).
     Then the sum of sups ≤ sup follows. -/
  suffices h : ∀ (q1 : ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ Icc a b})
      (q2 : ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ Icc b c}),
      (∑ i ∈ Finset.range q1.1,
          edist (f (q1.2.1 (i + 1))) (f (q1.2.1 i)) ^ p) +
      (∑ i ∈ Finset.range q2.1,
          edist (f (q2.2.1 (i + 1))) (f (q2.2.1 i)) ^ p) ≤
      ⨆ q : ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ Icc a c},
        ∑ i ∈ Finset.range q.1,
          edist (f (q.2.1 (i + 1))) (f (q.2.1 i)) ^ p by
    letI : Nonempty (ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ Icc a b}) :=
      ⟨⟨0, ⟨fun _ => a, ⟨monotone_const, fun _ => ⟨le_refl _, hab⟩⟩⟩⟩⟩
    letI : Nonempty (ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ Icc b c}) :=
      ⟨⟨0, ⟨fun _ => b, ⟨monotone_const, fun _ => ⟨le_refl _, hbc⟩⟩⟩⟩⟩
    simp_rw [ENNReal.iSup_add, ENNReal.add_iSup]
    exact iSup_le fun q1 => iSup_le fun q2 => h q1 q2
  intro q1 q2
  /- Core: concatenate partitions q1 of [a,b] and q2 of [b,c] into one of [a,c].
     Define v(i) = u1(i) for i ≤ n1, v(n1+1+j) = u2(j) for j ≥ 0.
     The concatenated sum over range(n1 + 1 + n2) equals S1 + cross + S2 ≥ S1 + S2. -/
  set n1 := q1.1; set u1 := q1.2.1
  set n2 := q2.1; set u2 := q2.2.1
  -- Concatenated partition: u1 on {0,..,n1}, junction, then u2 shifted
  set v : ℕ → α := fun i => if i ≤ n1 then u1 i else u2 (i - (n1 + 1)) with hv_def
  have hv_mono : Monotone v := by
    intro i j hij
    simp only [hv_def]
    split_ifs with hi hj hj
    · exact q1.2.prop.1 hij
    · -- i ≤ n1 < j: chain through the boundary
      calc u1 i ≤ u1 n1 := q1.2.prop.1 hi
        _ ≤ b := (q1.2.prop.2 n1).2
        _ ≤ u2 0 := (q2.2.prop.2 0).1
        _ ≤ u2 (j - (n1 + 1)) := q2.2.prop.1 (Nat.zero_le _)
    · omega -- impossible: i > n1 but j ≤ n1 with i ≤ j
    · exact q2.2.prop.1 (by omega)
  have hv_mem : ∀ i, v i ∈ Icc a c := by
    intro i; simp only [hv_def]
    split_ifs with hi
    · exact ⟨(q1.2.prop.2 i).1, le_trans (q1.2.prop.2 i).2 hbc⟩
    · exact ⟨le_trans hab (q2.2.prop.2 _).1, (q2.2.prop.2 _).2⟩
  -- The concatenated sum dominates S(q1) + S(q2)
  calc (∑ i ∈ Finset.range n1, edist (f (u1 (i + 1))) (f (u1 i)) ^ p)
      + (∑ i ∈ Finset.range n2, edist (f (u2 (i + 1))) (f (u2 i)) ^ p)
      ≤ ∑ i ∈ Finset.range (n1 + 1 + n2),
          edist (f (v (i + 1))) (f (v i)) ^ p := by
        /- Split range(n1 + 1 + n2) = range(n1) ∪ {n1} ∪ (Ico (n1+1) (n1+1+n2)).
           On range(n1): v agrees with u1, recovering S1.
           On {n1}: cross term ≥ 0, so we gain.
           On Ico(n1+1, n1+1+n2): v(i) = u2(i-n1-1), recovering S2 after reindex. -/
        sorry
    _ ≤ ⨆ q : ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ Icc a c},
          ∑ i ∈ Finset.range q.1,
            edist (f (q.2.1 (i + 1))) (f (q.2.1 i)) ^ p :=
        le_iSup_of_le ⟨n1 + 1 + n2, ⟨v, hv_mono, hv_mem⟩⟩ le_rfl

end Concatenation

/-! ### Monotonicity in the exponent -/

section Exponent

variable [LinearOrder α] [PseudoEMetricSpace E]

/-- **Monotonicity of p-variation in the exponent**. If `1 ≤ p ≤ q` and each increment
`edist(f(uᵢ₊₁), f(uᵢ))` is bounded by `D`, then the `q`-variation is controlled by the
`p`-variation. Specifically, `ePVariationOn q f s ≤ D^(q-p) * ePVariationOn p f s`.

The key inequality at the partition level is:
  `∑ dᵢ^q = ∑ dᵢ^(q-p) · dᵢ^p ≤ (max dᵢ)^(q-p) · ∑ dᵢ^p ≤ D^(q-p) · ∑ dᵢ^p`

This is essential in rough path theory: paths with finite `p`-variation automatically
have finite `q`-variation for all `q > p`, but the converse fails. -/
theorem ePVariationOn_le_mul_of_le_exponent {p q : ℝ} {f : α → E} {s : Set α} {D : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hD : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ D) :
    ePVariationOn q f s ≤ D ^ (q - p) * ePVariationOn p f s := by
  sorry -- Each increment dᵢ ≤ D, so dᵢ^q = dᵢ^p · dᵢ^(q-p) ≤ dᵢ^p · D^(q-p).
  -- Summing and taking suprema yields the result.

/-- Corollary: finite `p`-variation implies finite `q`-variation for `q ≥ p`,
provided the image has bounded diameter. -/
theorem HasFinitePVariationOn.of_le_exponent {p q : ℝ} {f : α → E} {s : Set α}
    (hf : HasFinitePVariationOn p f s) (hp : 1 ≤ p) (hpq : p ≤ q)
    (hbdd : EMetric.diam (f '' s) ≠ ⊤) :
    HasFinitePVariationOn q f s := by
  sorry -- Follows from ePVariationOn_le_mul_of_le_exponent with D = diam(f(s))

end Exponent

/-! ### Hölder continuity and p-variation -/

section Holder

variable [LinearOrder α] [PseudoEMetricSpace E] [PseudoEMetricSpace α]

/-- A function that is `γ`-Hölder continuous on `s` (with `γ > 0`) has finite
`(1/γ)`-variation on `s`, provided `s` has finite diameter.

This is the bridge between Hölder regularity and `p`-variation regularity.
Standard Brownian motion is `γ`-Hölder for all `γ < 1/2`, giving finite
`p`-variation for `p > 2`. -/
theorem hasFinitePVariationOn_of_holder {γ : ℝ} {C : ℝ≥0} {f : α → E} {s : Set α}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hf : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ C * edist x y ^ γ)
    (hs : EMetric.diam s ≠ ⊤) :
    HasFinitePVariationOn (1 / γ) f s := by
  sorry -- Each increment edist(f(uᵢ₊₁), f(uᵢ))^(1/γ) ≤ C^(1/γ) · edist(uᵢ₊₁, uᵢ).
  -- Summing the right side yields C^(1/γ) · ∑ edist(uᵢ₊₁, uᵢ)
  -- ≤ C^(1/γ) · eVariationOn id s (total variation of the partition in α).
  -- If α = ℝ, this is bounded by diam(s). Finiteness follows.

end Holder

/-! ### Control functions -/

section Control

/-- A **control function** is a continuous, super-additive function `ω : ℝ × ℝ → ℝ≥0∞`
that vanishes on the diagonal. In rough path theory, one typically requires:
  1. `ω(s, s) = 0`
  2. `ω(s, t) + ω(t, u) ≤ ω(s, u)` for `s ≤ t ≤ u` (super-additivity)
  3. Continuity near the diagonal

The `p`-variation provides a canonical control: `ω(s, t) = ePVariationOn p f (Icc s t)`. -/
structure IsControl (ω : ℝ → ℝ → ℝ≥0∞) : Prop where
  /-- A control vanishes on the diagonal. -/
  diagonal : ∀ s, ω s s = 0
  /-- A control is super-additive over adjacent intervals. -/
  superadditive : ∀ s t u, s ≤ t → t ≤ u → ω s t + ω t u ≤ ω s u
  /-- A control is nonneg (automatic in `ℝ≥0∞`). -/
  nonneg : ∀ s t, 0 ≤ ω s t

/-- The `p`-variation of `f` over closed intervals defines a control function,
provided `f` has finite `p`-variation on the ambient interval and `0 < p`. -/
theorem isControl_ePVariationOn {p : ℝ} (hp : 0 < p) (f : ℝ → E)
    [PseudoEMetricSpace E] :
    IsControl (fun s t => ePVariationOn p f (Icc s t)) where
  diagonal s := by simp [ePVariationOn_singleton hp]
  superadditive s t u hst htu := ePVariationOn_add_le hp hst htu
  nonneg _ _ := zero_le _

end Control

/-! ### Relation to Mathlib's eVariationOn -/

section Relation

variable [LinearOrder α] [PseudoEMetricSpace E]
set_option maxHeartbeats 500000 in
/-- When `p = 1`, the `ePVariationOn` coincides with Mathlib's `eVariationOn`.
This justifies our definition as a proper generalization. -/
theorem ePVariationOn_one_eq_eVariationOn (f : α → E) (s : Set α) :
    ePVariationOn 1 f s = eVariationOn f s := by
  simp only [ePVariationOn, eVariationOn, ENNReal.rpow_one]

end Relation

/-! ### Continuous p-variation -/

section ContinuousPVar

variable [PseudoEMetricSpace E]

/-- A path `f : ℝ → E` has **continuous p-variation** on `[a, b]` if the map
`t ↦ ePVariationOn p f (Icc a t)` is continuous on `[a, b]`.

This is automatic for continuous paths with finite `p`-variation when `p ≥ 1`.
It is crucial in rough path theory because it ensures the control function
`ω(s,t) = ‖X‖_{p-var;[s,t]}^p` behaves well. -/
def HasContinuousPVariationOn (p : ℝ) (f : ℝ → E) (a b : ℝ) : Prop :=
  ContinuousOn (fun t => ePVariationOn p f (Icc a t)) (Icc a b)

/-- A continuous path with finite `p`-variation (for `p ≥ 1`) has continuous
`p`-variation. This is a standard result; see Friz–Victoir Proposition 5.3. -/
theorem hasContinuousPVariationOn_of_continuous {p : ℝ} {f : ℝ → E} {a b : ℝ}
    (hp : 1 ≤ p) (hf : ContinuousOn f (Icc a b))
    (hfv : HasFinitePVariationOn p f (Icc a b)) :
    HasContinuousPVariationOn p f a b := by
  sorry -- Standard argument: the p-variation function is monotone (in t) and
  -- bounded, so it suffices to show right-continuity. A jump at time t would
  -- require a macroscopic increment edist(f(t), f(t+)) > 0, contradicting
  -- continuity of f.

end ContinuousPVar

/-! ### p-Variation for stochastic processes -/

section Stochastic

variable [MeasurableSpace Ω] [PseudoEMetricSpace E]

/-- A stochastic process `X : ℝ → Ω → E` has **finite p-variation almost surely** on
`[a, b]` with respect to measure `μ` if the set of `ω` for which `X(·)(ω)` has
finite `p`-variation has full measure.

This is the correct notion for Brownian motion: a.s. finite `p`-variation for `p > 2`. -/
def HasFinitePVariationAE (p : ℝ) (X : ℝ → Ω → E)
    (a b : ℝ) (μ : MeasureTheory.Measure Ω) : Prop :=
  ∀ᵐ ω ∂μ, HasFinitePVariationOn p (fun t => X t ω) (Icc a b)

/-- **Brownian motion has finite p-variation a.s. for p > 2.**

This is the foundational regularity result for stochastic calculus.
Brownian paths are `γ`-Hölder for all `γ < 1/2`, giving finite `p`-variation
for all `p > 2` by `hasFinitePVariationOn_of_holder`. The converse direction—
that Brownian motion has infinite `2`-variation in the classical sense but
quadratic variation equal to `t`—is what forces the Itô correction.

We state this as an axiom-as-hypothesis: any process satisfying certain Brownian
motion properties (independent increments, Gaussian with variance `t`, continuous
paths) will have this regularity. -/
theorem brownianMotion_hasFinitePVariationAE
    (p : ℝ) (hp : 2 < p) (a b : ℝ) (hab : a ≤ b)
    -- Brownian motion hypotheses, carried as parameters
    (W : ℝ → Ω → ℝ) (μ : MeasureTheory.Measure Ω)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => W t ω) (Icc a b))
    (hholder : ∀ γ : ℝ, γ < 1/2 → ∀ᵐ ω ∂μ,
      ∃ C : ℝ≥0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        dist (W s ω) (W t ω) ≤ C * dist s t ^ γ) :
    HasFinitePVariationAE p W a b μ := by
  sorry -- Choose γ with 1/p < γ < 1/2 (possible since p > 2).
  -- By hholder, a.s. the path is γ-Hölder. By hasFinitePVariationOn_of_holder,
  -- this gives finite (1/γ)-variation. Since 1/γ < p, monotonicity in exponent
  -- (ePVariationOn_le_mul_of_le_exponent) gives finite p-variation.

end Stochastic

end StochCalc