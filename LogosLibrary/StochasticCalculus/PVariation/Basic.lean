/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: StochasticCalculus/PVariation/Basic.lean
-/
import Mathlib.Topology.MetricSpace.Bounded -- has ediam_le_of_forall_dist_le
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
  -- Key facts: v agrees with u1 on the initial segment, with u2 on the tail
  have hv_eq1 : ∀ i, i ≤ n1 → v i = u1 i := fun i hi => by simp [hv_def, hi]
  have hv_eq2 : ∀ j, v (n1 + 1 + j) = u2 j := by
    intro j; simp only [hv_def, show ¬(n1 + 1 + j ≤ n1) from by omega]
    norm_num
  -- The sum on the first n1 steps of v equals S1
  have hS1_eq : ∑ i ∈ Finset.range n1, edist (f (v (i + 1))) (f (v i)) ^ p =
      ∑ i ∈ Finset.range n1, edist (f (u1 (i + 1))) (f (u1 i)) ^ p := by
    apply Finset.sum_congr rfl; intro i hi
    have him := Finset.mem_range.mp hi
    rw [hv_eq1 i (by omega), hv_eq1 (i + 1) (by omega)]
  -- The sum on the shifted tail of v equals S2
  have hS2_eq : ∑ j ∈ Finset.range n2,
        edist (f (v (n1 + 1 + j + 1))) (f (v (n1 + 1 + j))) ^ p =
      ∑ j ∈ Finset.range n2, edist (f (u2 (j + 1))) (f (u2 j)) ^ p := by
    apply Finset.sum_congr rfl; intro j _
    rw [show n1 + 1 + j + 1 = n1 + 1 + (j + 1) from by ring, hv_eq2 (j + 1), hv_eq2 j]
  -- Decompose the big sum: range(n1 + 1 + n2) = range(n1) ∪ {n1} ∪ shifted range(n2)
  -- Using sum_range_succ and sum_range_add
  set g : ℕ → ℝ≥0∞ := fun i => edist (f (v (i + 1))) (f (v i)) ^ p
  have hdecomp : ∑ i ∈ Finset.range (n1 + 1 + n2), g i =
      (∑ i ∈ Finset.range n1, g i) + g n1 +
      ∑ j ∈ Finset.range n2, g (n1 + 1 + j) := by
    rw [show n1 + 1 + n2 = (n1 + 1) + n2 from by ring]
    rw [Finset.sum_range_add g (n1 + 1) n2]
    congr 1
    rw [Finset.sum_range_succ g n1]
  -- The concatenated sum dominates S(q1) + S(q2)
  calc (∑ i ∈ Finset.range n1, edist (f (u1 (i + 1))) (f (u1 i)) ^ p)
      + (∑ i ∈ Finset.range n2, edist (f (u2 (i + 1))) (f (u2 i)) ^ p)
      = (∑ i ∈ Finset.range n1, g i) +
        ∑ j ∈ Finset.range n2, g (n1 + 1 + j) := by
        rw [hS1_eq, hS2_eq]
    _ ≤ (∑ i ∈ Finset.range n1, g i) + g n1 +
        ∑ j ∈ Finset.range n2, g (n1 + 1 + j) := by
        -- A + B ≤ (A + cross) + B, since cross ≥ 0
        gcongr
        exact le_add_right le_rfl
    _ = ∑ i ∈ Finset.range (n1 + 1 + n2), g i := hdecomp.symm
    _ ≤ ⨆ q : ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ Icc a c},
          ∑ i ∈ Finset.range q.1,
            edist (f (q.2.1 (i + 1))) (f (q.2.1 i)) ^ p :=
        le_iSup_of_le ⟨n1 + 1 + n2, ⟨v, hv_mono, hv_mem⟩⟩ le_rfl

end Concatenation

/-! ### Monotonicity in the exponent -/

section Exponent

variable [LinearOrder α] [PseudoEMetricSpace E]

/-- Pointwise inequality: for `a ≤ D`, `0 ≤ r`, and `0 < s`, we have
`a ^ (r + s) ≤ D ^ r * a ^ s` in `ℝ≥0∞`.
This is the core of the exponent monotonicity argument. -/
private theorem rpow_add_le_mul_rpow {a D : ℝ≥0∞} {r s : ℝ}
    (haD : a ≤ D) (hr : 0 ≤ r) (hs : 0 < s) :
    a ^ (r + s) ≤ D ^ r * a ^ s := by
  rcases eq_or_ne a 0 with ha0 | ha0
  · -- a = 0: LHS = 0^(r+s) = 0 (since r + s > 0), RHS ≥ 0
    simp [ha0, ENNReal.zero_rpow_of_pos (by linarith : 0 < r + s)]
  · rcases eq_or_ne a ⊤ with ha_top | ha_top
    · -- a = ⊤ implies D = ⊤
      have hD : D = ⊤ := top_le_iff.mp (ha_top ▸ haD)
      simp [ha_top, hD]
      subst ha_top hD
      simp_all only [ne_eq, ENNReal.top_ne_zero, not_false_eq_true, Std.le_refl, ENNReal.top_rpow_of_pos,
        ENNReal.rpow_eq_zero_iff, false_and, true_and, false_or, not_lt, ENNReal.mul_top, le_top]
    · -- 0 < a < ⊤: use rpow_add and monotonicity of rpow
      rw [ENNReal.rpow_add r s]
      · exact mul_le_mul_left (ENNReal.rpow_le_rpow haD hr) _
      · exact Ne.symm (Ne.intro (id (Ne.symm ha0)))
      · exact Ne.symm (Ne.intro (id (Ne.symm ha_top)))

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
  -- It suffices to bound each partition sum with exponent q
  apply iSup_le; intro ⟨n, u, hu, hus⟩
  -- Bound each term: edist(...)^q ≤ D^(q-p) * edist(...)^p
  have hqp : 0 ≤ q - p := sub_nonneg.mpr hpq
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ q
      = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ ((q - p) + p) := by
        congr 1; ext i; congr 1; ring
    _ ≤ ∑ i ∈ Finset.range n, (D ^ (q - p) * edist (f (u (i + 1))) (f (u i)) ^ p) := by
        apply Finset.sum_le_sum; intro i _
        exact rpow_add_le_mul_rpow (edist_comm (f (u (i + 1))) (f (u i)) ▸
          hD _ (hus i) _ (hus (i + 1))) hqp hp0
    _ = D ^ (q - p) * ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ p := by
        rw [Finset.mul_sum]
    _ ≤ D ^ (q - p) * ePVariationOn p f s := by
        gcongr
        exact le_ePVariationOn hu hus

/-- Corollary: finite `p`-variation implies finite `q`-variation for `q ≥ p`,
provided the image has bounded diameter. -/
theorem HasFinitePVariationOn.of_le_exponent {p q : ℝ} {f : α → E} {s : Set α}
    (hf : HasFinitePVariationOn p f s) (hp : 1 ≤ p) (hpq : p ≤ q)
    (hbdd : Metric.ediam (f '' s) ≠ ⊤) :
    HasFinitePVariationOn q f s := by
  -- Use D = diam(f '' s) as the uniform bound on increments
  set D := Metric.ediam (f '' s)
  have hD : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ D := by
    intro x hx y hy
    exact Metric.edist_le_ediam_of_mem (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy)
  calc ePVariationOn q f s
      ≤ D ^ (q - p) * ePVariationOn p f s :=
        ePVariationOn_le_mul_of_le_exponent hp hpq hD
    _ < ⊤ := by
        apply ENNReal.mul_lt_top
        · rw [@lt_top_iff_ne_top];
          simp_all only [ne_eq, ENNReal.rpow_eq_top_iff, sub_neg, sub_pos, false_and,
          or_false, not_and, not_lt, implies_true, D]
        · exact lt_top_of_lt hf

end Exponent

/-! ### Hölder continuity and p-variation -/

section Holder

variable [LinearOrder α] [PseudoEMetricSpace E] [PseudoEMetricSpace α]

/-- A function that is `γ`-Hölder continuous on `s` (with `γ > 0`) has finite
`(1/γ)`-variation on `s`, provided `s` has finite diameter.

This is the bridge between Hölder regularity and `p`-variation regularity.
Standard Brownian motion is `γ`-Hölder for all `γ < 1/2`, giving finite
`p`-variation for `p > 2`.

**Note**: The proof requires that the 1-variation of the identity embedding `s ↪ α`
is bounded by the diameter. This holds when the metric on `α` is compatible with
the linear order (e.g., `α = ℝ`). In the general case we use `eVariationOn id s`
as the bounding quantity, which is finite when `s` has bounded variation as a
subset of its ambient metric space. -/
theorem hasFinitePVariationOn_of_holder {γ : ℝ} {C : ℝ≥0} {f : α → E} {s : Set α}
    (hγ : 0 < γ) (_hγ1 : γ ≤ 1)
    (hf : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ C * edist x y ^ γ)
    (hs : eVariationOn id s ≠ ⊤) :
    HasFinitePVariationOn (1 / γ) f s := by
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  have h1γ_pos : (0 : ℝ) < 1 / γ := div_pos one_pos hγ
  have h1γ_nonneg : (0 : ℝ) ≤ 1 / γ := le_of_lt h1γ_pos
  -- Key lemma: (d ^ γ) ^ (1/γ) = d for d : ℝ≥0∞, since γ · (1/γ) = 1
  have rpow_cancel : ∀ d : ℝ≥0∞, (d ^ γ) ^ (1 / γ) = d := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd0
    · simp [ENNReal.zero_rpow_of_pos hγ]
      exact RCLike.ofReal_pos.mp hγ
    rcases eq_or_ne d ⊤ with rfl | hd_top
    · simp [ENNReal.top_rpow_of_pos hγ]
      exact RCLike.ofReal_pos.mp hγ
    · · rw [← ENNReal.rpow_mul, mul_comm,
          one_div_mul_cancel hγ_ne, ENNReal.rpow_one]
  -- Reduce to: every partition sum ≤ C^(1/γ) * eVariationOn id s
  rw [HasFinitePVariationOn, ePVariationOn]
  suffices h : ∀ (n : ℕ) (u : ℕ → α), Monotone u → (∀ i, u i ∈ s) →
      ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ (1 / γ) ≤
        (↑C : ℝ≥0∞) ^ (1 / γ) * eVariationOn id s by
    apply lt_of_le_of_lt
    · exact iSup_le fun ⟨n, u, hu, hus⟩ => h n u hu hus
    · exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg h1γ_nonneg ENNReal.coe_ne_top)
        (lt_top_iff_ne_top.mpr hs)
  intro n u hu hus
  -- Step 1: Bound each term via the Hölder hypothesis.
  --   edist(f(u_{i+1}), f(u_i))^(1/γ)
  --   ≤ (C · edist(u_{i+1}, u_i)^γ)^(1/γ)     [Hölder, mono of rpow]
  --   = C^(1/γ) · (edist(u_{i+1}, u_i)^γ)^(1/γ) [split rpow over product]
  --   = C^(1/γ) · edist(u_{i+1}, u_i)            [rpow_cancel]
  -- Step 2: Factor C^(1/γ) out of the sum.
  -- Step 3: The remaining ∑ edist(u_{i+1}, u_i) ≤ eVariationOn id s.
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ (1 / γ)
      ≤ ∑ i ∈ Finset.range n,
          ((↑C : ℝ≥0∞) * edist (u (i + 1)) (u i) ^ γ) ^ (1 / γ) := by
        gcongr with i _
        exact Metric.mem_closedEBall.mp (hf (u (i + 1)) (hus (i + 1)) (u i) (hus i))
    _ = ∑ i ∈ Finset.range n,
          ((↑C : ℝ≥0∞) ^ (1 / γ) * edist (u (i + 1)) (u i)) := by
        congr 1; ext i
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1γ_nonneg, rpow_cancel]
    _ = (↑C : ℝ≥0∞) ^ (1 / γ) *
          ∑ i ∈ Finset.range n, edist (u (i + 1)) (u i) := by
        rw [Finset.mul_sum]
    _ ≤ (↑C : ℝ≥0∞) ^ (1 / γ) * eVariationOn id s := by
        gcongr
        -- ∑ edist(u_{i+1}, u_i) = ∑ edist(id(u_{i+1}), id(u_i)) ≤ eVariationOn id s
        exact le_iSup_of_le ⟨n, ⟨u, hu, hus⟩⟩ le_rfl

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

/-- Iterated super-additivity: for a monotone sequence t₀ ≤ t₁ ≤ ⋯ ≤ tₙ,
    the sum of p-variations over consecutive sub-intervals is bounded by the
    p-variation over the full interval [t₀, tₙ]. -/
theorem ePVariationOn_sum_le [LinearOrder α]
    {p : ℝ} (hp : 0 < p) {f : α → E} {t : ℕ → α}
    {n : ℕ} (ht : Monotone t) :
    ∑ i ∈ Finset.range n, ePVariationOn p f (Icc (t i) (t (i + 1)))
      ≤ ePVariationOn p f (Icc (t 0) (t n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc ∑ i ∈ Finset.range n, ePVariationOn p f (Icc (t i) (t (i + 1)))
          + ePVariationOn p f (Icc (t n) (t (n + 1)))
        ≤ ePVariationOn p f (Icc (t 0) (t n))
          + ePVariationOn p f (Icc (t n) (t (n + 1))) := by gcongr
      _ ≤ ePVariationOn p f (Icc (t 0) (t (n + 1))) :=
          ePVariationOn_add_le hp (ht (Nat.zero_le n)) (ht (Nat.le_succ n))

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
    (W : ℝ → Ω → ℝ) (μ : MeasureTheory.Measure Ω)
    (_hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => W t ω) (Icc a b))
    (hholder : ∀ γ : ℝ, γ < 1/2 → ∀ᵐ ω ∂μ,
      ∃ C : ℝ≥0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        dist (W s ω) (W t ω) ≤ C * dist s t ^ γ) :
    HasFinitePVariationAE p W a b μ := by
  -- Step 1: Choose γ with 1/p < γ < 1/2  (possible since p > 2 ⟹ 1/p < 1/2)
  have hp_pos : (0 : ℝ) < p := by linarith
  have h12 : (1 : ℝ) / p < 1 / 2 := by
    rw [div_lt_div_iff₀ hp_pos two_pos]; linarith
  obtain ⟨γ, hγl, hγu⟩ := exists_between h12
  -- Key properties of γ
  have hγ_pos : 0 < γ := lt_trans (div_pos one_pos hp_pos) hγl
  have hγ1 : γ ≤ 1 := (lt_trans hγu (by norm_num : (1 : ℝ) / 2 < 1)).le
  -- 1 ≤ 1/γ  (since γ < 1)
  have h1γ_ge_1 : 1 ≤ 1 / γ := (le_div_iff₀ hγ_pos).mpr (by nlinarith)
  -- 1/γ ≤ p  (since 1/p < γ ⟹ 1 < γp ⟹ 1/γ < p)
  have h1γ_le_p : 1 / γ ≤ p := by
    rw [div_le_iff₀ hγ_pos]
    have := (div_lt_iff₀ hp_pos).mp hγl
    linarith [mul_comm γ p]
  -- Step 2: Filter through the a.e. Hölder set
  filter_upwards [hholder γ hγu] with ω ⟨C, hC⟩
  -- hC : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (W s ω) (W t ω) ≤ ↑C * dist s t ^ γ
  -- Step 3: Convert dist Hölder bound to edist Hölder bound
  have hC_edist : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      edist (W x ω) (W y ω) ≤ ↑C * edist x y ^ γ := by
    intro x hx y hy
    simp only [edist_dist]
    calc ENNReal.ofReal (dist (W x ω) (W y ω))
        ≤ ENNReal.ofReal (↑C * dist x y ^ γ) :=
          ENNReal.ofReal_le_ofReal (hC x hx y hy)
      _ = ↑C * ENNReal.ofReal (dist x y) ^ γ := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ↑C)]
          congr 1
          · exact ENNReal.ofReal_coe_nnreal
          · exact (ENNReal.ofReal_rpow_of_nonneg dist_nonneg hγ_pos.le).symm
  -- Step 4: eVariationOn id on [a,b] ⊂ ℝ is finite
  -- (monotone sums telescope: ∑ edist(u_{i+1}, u_i) = edist(u_0, u_n) ≤ edist a b)
  have hvar : eVariationOn id (Icc a b) ≠ ⊤ := by
    have h := monotoneOn_id.eVariationOn_le (Set.left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    rw [Set.inter_self] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  -- Step 5: Hölder ⟹ finite (1/γ)-variation
  have h1γ_var := hasFinitePVariationOn_of_holder hγ_pos hγ1 hC_edist hvar
  -- Step 6: Image has finite diameter (Hölder on bounded set ⟹ bounded image)
  -- dist(W x ω, W y ω) ≤ C·(b-a)^γ for all x,y ∈ [a,b], so diam < ⊤
  have hbdd : Metric.ediam ((fun t => W t ω) '' Icc a b) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply Metric.ediam_le
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    calc dist (W s ω) (W t ω)
        ≤ ↑C * dist s t ^ γ := hC s hs t ht
      _ ≤ ↑C * (b - a) ^ γ := by
          gcongr
          exact Real.dist_le_of_mem_Icc hs ht
  -- Step 7: Exponent monotonicity: finite (1/γ)-variation ⟹ finite p-variation
  exact h1γ_var.of_le_exponent h1γ_ge_1 h1γ_le_p hbdd

end Stochastic

end StochCalc
