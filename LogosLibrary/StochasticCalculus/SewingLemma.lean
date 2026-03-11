/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: StochasticCalculus/SewingLemma.lean
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import LogosLibrary.StochasticCalculus.PVariation
/-!
# The Sewing Lemma

The **Sewing Lemma** is the fundamental analytical tool in rough path theory. It provides
a systematic way to construct additive functionals from "almost additive" approximations.

Given a two-parameter map `Ξ : ℝ → ℝ → E` (thought of as an approximate integral over `[s, t]`)
whose *defect from additivity*

  `δΞ(s, u, t) := Ξ(s, t) - Ξ(s, u) - Ξ(u, t)`

is controlled by `ω(s, t)^θ` for some control `ω` and exponent `θ > 1`, the Sewing Lemma
asserts the existence of a unique *additive* functional `I` satisfying:

  `‖I(s, t) - Ξ(s, t)‖ ≤ C · ω(s, t)^θ`

with `C = 1 / (2^(θ-1) - 1)`.

## The construction

The sewn map is built as the limit of dyadic Riemann sums. For a partition
`s = t₀ < t₁ < ⋯ < t_n = t`, the Riemann sum is `∑ᵢ Ξ(tᵢ, tᵢ₊₁)`. The key estimate is
that successive dyadic refinements form a Cauchy sequence: the difference between the
`n`-th and `(n+1)`-th dyadic refinement is bounded by `C · ω(s, t)^θ · 2^{-n(θ-1)}`,
which is summable precisely because `θ > 1`.

## Main definitions

* `StochCalc.sewingDefect Ξ s u t`: the defect `Ξ(s, t) - Ξ(s, u) - Ξ(u, t)`.
* `StochCalc.SewingCondition Ξ ω θ a b`: the hypothesis bundle asserting that `Ξ`
  has `θ`-controlled defect with respect to control `ω` on `[a, b]`.
* `StochCalc.sewingMap`: the unique additive map produced by the Sewing Lemma.

## Main results

* `StochCalc.sewingMap_additive`: the sewn map is additive.
* `StochCalc.sewingMap_dist_le`: the approximation bound
  `‖sewingMap Ξ s t - Ξ(s, t)‖ ≤ C · ω(s, t)^θ`.
* `StochCalc.sewingMap_unique`: uniqueness of the sewn map among additive functionals
  satisfying the approximation bound.

## References

* [Feyel, D.; de La Pradelle, A., *Curvilinear integrals along enriched paths*][feyel2006]
* [Gubinelli, M., *Controlling rough paths*][gubinelli2004]
* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Theorem 2.2][friz2020]

## Tags

sewing lemma, rough path, additive functional, almost additive, Gubinelli, control function
-/

noncomputable section

open Real --NNReal

open Set Filter

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### Defect of a two-parameter map -/

section Defect

/-- The **defect** (or **coboundary**) of a two-parameter map `Ξ` at the triple `(s, u, t)`.
This measures how far `Ξ` is from being additive:
  `δΞ(s, u, t) = Ξ(s, t) - Ξ(s, u) - Ξ(u, t)`.

If `Ξ` were a true integral `∫_s^t f`, then `δΞ ≡ 0`.
The Sewing Lemma says that when `δΞ` is small enough (controlled by `ω^θ` with `θ > 1`),
there exists a unique additive `I` close to `Ξ`. -/
def sewingDefect (Ξ : ℝ → ℝ → E) (s u t : ℝ) : E :=
  Ξ s t - Ξ s u - Ξ u t

@[simp]
theorem sewingDefect_self_left (Ξ : ℝ → ℝ → E) (hΞ : ∀ s, Ξ s s = 0) (s t : ℝ) :
    sewingDefect Ξ s s t = 0 := by
  simp [sewingDefect, hΞ]

@[simp]
theorem sewingDefect_self_right (Ξ : ℝ → ℝ → E) (hΞ : ∀ s, Ξ s s = 0) (s t : ℝ) :
    sewingDefect Ξ s t t = 0 := by
  simp [sewingDefect, hΞ, sub_self]

variable {E : Type*} [NormedAddCommGroup E]
/-- The defect satisfies a **cocycle identity**: the defect of the defect telescopes.
For `s ≤ u ≤ v ≤ t`:
  `δΞ(s, u, t) = δΞ(s, u, v) + δΞ(s, v, t) + δΞ(u, v, t)`.

This identity is what makes the dyadic refinement argument work: each refinement step
introduces defects at one scale, and the cocycle identity controls how they accumulate. -/
theorem sewingDefect_add (Ξ : ℝ → ℝ → E) (s u v t : ℝ) :
    sewingDefect Ξ s u t = sewingDefect Ξ s u v + sewingDefect Ξ s v t - sewingDefect Ξ u v t := by
  simp only [sewingDefect]
  abel

end Defect

/-! ### Sewing condition -/

section SewingCondition

/-- The **Sewing Condition**: the hypotheses required by the Sewing Lemma.

A two-parameter map `Ξ` satisfies the sewing condition with control `ω`, exponent `θ`,
and constant `K` on `[a, b]` if:

1. `Ξ(s, s) = 0` for all `s` (normalization),
2. `‖δΞ(s, u, t)‖ ≤ K · ω(s, t)^θ` for all `a ≤ s ≤ u ≤ t ≤ b` (defect bound),
3. `θ > 1` (the critical exponent condition — this is what makes the geometric series converge),
4. `ω` is super-additive and vanishes on the diagonal (control axioms).

The exponent condition `θ > 1` is sharp: for `θ = 1`, the defect sums diverge logarithmically,
and for `θ < 1` they diverge polynomially. This is why one needs "two levels of regularity"
in rough path theory — one level of Hölder regularity is not enough.

Note: we carry `K` explicitly rather than folding it into `ω` for flexibility. -/
structure SewingCondition (Ξ : ℝ → ℝ → E) (ω : ℝ → ℝ → ℝ) (θ K : ℝ) (a b : ℝ) : Prop where
  /-- The map vanishes on the diagonal. -/
  vanish_diag : ∀ s, Ξ s s = 0
  /-- The exponent is strictly greater than 1. -/
  one_lt_theta : 1 < θ
  /-- The constant is nonneg. -/
  K_nonneg : 0 ≤ K
  /-- The control is nonneg. -/
  omega_nonneg : ∀ s t, 0 ≤ ω s t
  /-- The control vanishes on the diagonal. -/
  omega_diag : ∀ s, ω s s = 0
  /-- The control is super-additive. -/
  omega_superadd : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ω s u + ω u t ≤ ω s t
  /-- The defect bound. -/
  defect_bound : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ‖sewingDefect Ξ s u t‖ ≤ K * ω s t ^ θ

end SewingCondition

/-! ### Dyadic Riemann sums -/

section DyadicSums

/-- The `n`-th dyadic partition point of `[s, t]`: the point `s + k · (t - s) / 2^n`. -/
def dyadicPoint (s t : ℝ) (n k : ℕ) : ℝ :=
  s + k * (t - s) / 2 ^ n

@[simp]
theorem dyadicPoint_zero (s t : ℝ) (n : ℕ) : dyadicPoint s t n 0 = s := by
  simp [dyadicPoint]

theorem dyadicPoint_last (s t : ℝ) (n : ℕ) : dyadicPoint s t n (2 ^ n) = t := by
  simp [dyadicPoint]

theorem dyadicPoint_mono {s t : ℝ} (hst : s ≤ t) (n : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    dyadicPoint s t n j ≤ dyadicPoint s t n k := by
  simp only [dyadicPoint]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  gcongr
  linarith

/-- The `n`-th dyadic Riemann sum of `Ξ` over `[s, t]`:
  `Sₙ(s, t) = ∑_{k=0}^{2ⁿ-1} Ξ(tₖ, tₖ₊₁)`
where `tₖ = s + k(t-s)/2ⁿ`. -/
def dyadicSum (Ξ : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) : E :=
  ∑ k ∈ Finset.range (2 ^ n), Ξ (dyadicPoint s t n k) (dyadicPoint s t n (k + 1))

@[simp]
theorem dyadicSum_zero (Ξ : ℝ → ℝ → E) (s t : ℝ) :
    dyadicSum Ξ s t 0 = Ξ s t := by
  simp [dyadicSum, dyadicPoint]

/-- **Key estimate**: the difference between successive dyadic refinements is controlled
by a geometric factor.

`‖S_{n+1}(s,t) - Sₙ(s,t)‖ ≤ K · 2^n · ω(s,t)^θ · 2^{-n·θ}`
                            `= K · ω(s,t)^θ · 2^{-n(θ-1)}`

Each dyadic interval at level `n` splits into two at level `n+1`, and the difference
between `Ξ(tₖ, tₖ₊₁)` and `Ξ(tₖ, mₖ) + Ξ(mₖ, tₖ₊₁)` is exactly `δΞ(tₖ, mₖ, tₖ₊₁)`,
bounded by `K · ω(tₖ, tₖ₊₁)^θ`. Summing over the `2^n` intervals and using
super-additivity of `ω` gives the result.

The factor `2^{-n(θ-1)}` is summable precisely because `θ > 1`. -/
theorem dyadicSum_diff_bound {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K : ℝ} {a b : ℝ}
    (hΞ : SewingCondition Ξ ω θ K a b) {s t : ℝ} (has : a ≤ s) (htb : t ≤ b)
    (hst : s ≤ t) (n : ℕ) :
    ‖dyadicSum Ξ s t (n + 1) - dyadicSum Ξ s t n‖ ≤
      K * ω s t ^ θ * (2⁻¹ : ℝ) ^ (n * (θ - 1)) := by
  sorry -- Proof sketch:
  -- 1. Rewrite S_{n+1} by pairing consecutive terms: for each k in range(2^n),
  --    the two terms at level n+1 are Ξ(t_{2k}, t_{2k+1}) + Ξ(t_{2k+1}, t_{2k+2}).
  -- 2. The difference from level n is:
  --    S_{n+1} - Sₙ = ∑_k [Ξ(t_{2k}, t_{2k+1}) + Ξ(t_{2k+1}, t_{2k+2}) - Ξ(tₖ, tₖ₊₁)]
  --                  = -∑_k δΞ(t_{2k}, t_{2k+1}, t_{2k+2})
  -- 3. Triangle inequality: ‖S_{n+1} - Sₙ‖ ≤ ∑_k K · ω(t_{2k}, t_{2k+2})^θ.
  -- 4. Since ω(t_{2k}, t_{2k+2}) ≤ ω(s,t)/2^n (by super-additivity applied n times),
  --    each term is bounded by K · (ω(s,t)/2^n)^θ = K · ω(s,t)^θ · 2^{-nθ}.
  -- 5. Summing 2^n such terms: total ≤ K · ω(s,t)^θ · 2^n · 2^{-nθ}
  --    = K · ω(s,t)^θ · 2^{-n(θ-1)}.

end DyadicSums

/-! ### The sewn map -/

section SewnMap

/-- The **sewn map** (or sewing integral): the limit of dyadic Riemann sums.

`sewingMap Ξ s t = lim_{n → ∞} Sₙ(s, t)`

where `Sₙ` is the `n`-th dyadic Riemann sum. The Sewing Lemma guarantees that this
limit exists when the sewing condition holds. -/
def sewingMap (Ξ : ℝ → ℝ → E) [CompleteSpace E] (ω : ℝ → ℝ → ℝ) (θ K : ℝ) (a b : ℝ)
    (_hΞ : SewingCondition Ξ ω θ K a b) (s t : ℝ) : E :=
  if _h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    -- In a complete space, the limit exists because the dyadic sums form a Cauchy sequence.
    -- We use `lim` from Mathlib's filter limit API.
    limUnder atTop (fun n => dyadicSum Ξ s t n)
  else
    0

/-- The geometric constant appearing in the Sewing Lemma bound.
`sewingConst θ = 1 / (2^(θ-1) - 1)`.

This is the sum of the geometric series `∑_{n=0}^∞ 2^{-n(θ-1)}`, which converges
precisely when `θ > 1`. For `θ = 3/2` (typical for Brownian motion level-2 data),
`sewingConst = 1/(√2 - 1) = √2 + 1 ≈ 2.41`. -/
def sewingConst (θ : ℝ) : ℝ :=
  1 / (2 ^ (θ - 1) - 1)

theorem sewingConst_pos {θ : ℝ} (hθ : 1 < θ) : 0 < sewingConst θ := by
  unfold sewingConst
  apply div_pos one_pos
  have hθ1 : (0 : ℝ) < θ - 1 := by linarith
  have : (1 : ℝ) < 2 ^ (θ - 1) := by
    conv_lhs => rw [show (1 : ℝ) = 2 ^ (0 : ℝ) by simp]
    exact rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hθ1
  linarith

/-- **The Sewing Lemma, existence part**: the dyadic Riemann sums converge.
The key estimate is that `{Sₙ}` is Cauchy:
  `‖S_m - S_n‖ ≤ K · sewingConst(θ) · ω(s,t)^θ · 2^{-min(m,n)·(θ-1)}`

This follows from summing the geometric bound on successive differences. -/
theorem dyadicSum_cauchy {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K : ℝ} {a b : ℝ}
    (hΞ : SewingCondition Ξ ω θ K a b) {s t : ℝ} (has : a ≤ s)
    (hst : s ≤ t) (htb : t ≤ b) :
    CauchySeq (fun n => dyadicSum Ξ s t n) := by
  apply cauchySeq_of_le_geometric ((2⁻¹ : ℝ) ^ (θ - 1)) (K * ω s t ^ θ)
  · exact rpow_lt_one (by positivity) (by norm_num : (2⁻¹ : ℝ) < 1)
      (by linarith [hΞ.one_lt_theta])
  · intro n
    rw [dist_eq_norm, norm_sub_rev]
    have h := dyadicSum_diff_bound hΞ has htb hst n
    calc ‖dyadicSum Ξ s t (n + 1) - dyadicSum Ξ s t n‖
        ≤ K * ω s t ^ θ * (2⁻¹ : ℝ) ^ (↑n * (θ - 1)) := h
      _ = K * ω s t ^ θ * ((2⁻¹ : ℝ) ^ (θ - 1)) ^ n := by
          congr 1
          rw [mul_comm (↑n : ℝ) (θ - 1), rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹),
              rpow_natCast]

/-- **The Sewing Lemma, approximation bound**: the sewn map is close to `Ξ`.

`‖sewingMap(s, t) - Ξ(s, t)‖ ≤ K · sewingConst(θ) · ω(s, t)^θ`

Proof: `sewingMap(s,t) - Ξ(s,t) = lim Sₙ - S₀ = ∑_{n=0}^∞ (S_{n+1} - Sₙ)`.
Each term is bounded by `K · ω(s,t)^θ · 2^{-n(θ-1)}`, and the geometric series
sums to `K · sewingConst(θ) · ω(s,t)^θ`. -/
theorem sewingMap_dist_le [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K : ℝ} {a b : ℝ}
    (hΞ : SewingCondition Ξ ω θ K a b) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖sewingMap Ξ ω θ K a b hΞ s t - Ξ s t‖ ≤
      K * sewingConst θ * ω s t ^ θ := by
  sorry -- The sewn map is the limit of Sₙ. We have:
  -- ‖lim Sₙ - S₀‖ = ‖∑_{n=0}^∞ (S_{n+1} - Sₙ)‖
  --               ≤ ∑_{n=0}^∞ ‖S_{n+1} - Sₙ‖
  --               ≤ ∑_{n=0}^∞ K · ω(s,t)^θ · 2^{-n(θ-1)}
  --               = K · ω(s,t)^θ · sewingConst(θ).

/-- **The Sewing Lemma, additivity**: the sewn map is additive.

`sewingMap(s, t) = sewingMap(s, u) + sewingMap(u, t)`  for `s ≤ u ≤ t`.

This is the payoff: starting from a merely *almost-additive* `Ξ`, we obtain a
*genuinely additive* `I`. The proof proceeds by showing that the dyadic sums are
"asymptotically additive": as the mesh refines, the sum over `[s, t]` approaches the
sum of the sums over `[s, u]` and `[u, t]`, because the defect terms vanish in the limit. -/
theorem sewingMap_additive [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K : ℝ} {a b : ℝ}
    (hΞ : SewingCondition Ξ ω θ K a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    sewingMap Ξ ω θ K a b hΞ s t =
      sewingMap Ξ ω θ K a b hΞ s u + sewingMap Ξ ω θ K a b hΞ u t := by
  sorry -- The general proof works by approximation: any additive functional I
  -- satisfying ‖I(s,t) - Ξ(s,t)‖ ≤ C · ω(s,t)^θ must be additive, because:
  -- ‖I(s,t) - I(s,u) - I(u,t)‖ ≤ ‖I(s,t) - Ξ(s,t)‖ + ‖Ξ(s,u) - I(s,u)‖
  --                                + ‖Ξ(u,t) - I(u,t)‖ + ‖δΞ(s,u,t)‖
  --                              ≤ 2C · ω(s,t)^θ + C · ω(s,u)^θ + C · ω(u,t)^θ
  -- Now iterate: subdivide [s,u] and [u,t] dyadically. At each step, the total bound
  -- shrinks by factor 2^{-(θ-1)} < 1, so in the limit it must be 0.


/-- **The Sewing Lemma, diagonal**: the sewn map vanishes on the diagonal. -/
theorem sewingMap_diag [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K : ℝ} {a b : ℝ}
    (hΞ : SewingCondition Ξ ω θ K a b) {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    sewingMap Ξ ω θ K a b hΞ s s = 0 := by
  unfold sewingMap
  rw [dif_pos ⟨has, le_refl s, hsb⟩]
  have hconst : ∀ n, dyadicSum Ξ s s n = 0 := by
    intro n
    simp only [dyadicSum, dyadicPoint, sub_self, mul_zero, zero_div, add_zero]
    simp [hΞ.vanish_diag]
  simp_rw [hconst]
  exact tendsto_const_nhds.limUnder_eq

/-- **The Sewing Lemma, uniqueness**: any additive functional satisfying the approximation
bound must equal the sewn map.

If `J` is additive on `[a, b]` and `‖J(s, t) - Ξ(s, t)‖ ≤ C · ω(s, t)^θ`, then `J = sewingMap`.

Proof: `‖J(s,t) - I(s,t)‖ ≤ ‖J(s,t) - Ξ(s,t)‖ + ‖Ξ(s,t) - I(s,t)‖ ≤ (C + C') · ω(s,t)^θ`.
Now use additivity of both `J` and `I` to subdivide `[s, t]` dyadically `n` times.
Each subdivision replaces `ω(s,t)^θ` with `2^n · ω(tₖ, tₖ₊₁)^θ`. By super-additivity,
`∑ ω(tₖ, tₖ₊₁)^θ ≤ ω(s,t)^θ / 2^{n(θ-1)} · 2^n = ω(s,t)^θ · 2^{-n(θ-1)}`.
Since `θ > 1`, this tends to 0, forcing `J = I`. -/
theorem sewingMap_unique [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K : ℝ} {a b : ℝ}
    (hΞ : SewingCondition Ξ ω θ K a b)
    {J : ℝ → ℝ → E} {C' : ℝ}
    (hJ_add : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      J s t = J s u + J u t)
    (hJ_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖J s t - Ξ s t‖ ≤ C' * ω s t ^ θ)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    J s t = sewingMap Ξ ω θ K a b hΞ s t := by
  sorry -- See docstring. The error after n dyadic subdivisions is bounded by
  -- (C' + K · sewingConst θ) · ω(s,t)^θ · 2^{-n(θ-1)}, which → 0.

end SewnMap

/-! ### The Sewing Lemma for the p-variation control -/

section PVarSewing

/-- **Sewing with p-variation control**. When the control `ω` is the `p`-variation
of some path, we get a version of the Sewing Lemma that interfaces directly with
the `p`-variation machinery from `StochCalc.PVariation`.

In practice, for a `1/p`-Hölder rough path `𝐗`, the natural control is
`ω(s,t) = ‖𝐗‖_{p-var;[s,t]}^p`, and the defect condition becomes
`‖δΞ(s,u,t)‖ ≤ K · ‖𝐗‖_{p-var;[s,t]}^(p·θ)`.

The condition `θ > 1` translates to `p · θ > p`, which for `p = 2` (Young regime)
or `p ∈ (2, 3)` (rough regime) gives the familiar exponent conditions. -/
theorem sewingCondition_of_pVar_control {Ξ : ℝ → ℝ → E} {f : ℝ → E}
    {p θ K : ℝ} {a b : ℝ}
    (hp : 1 ≤ p) (hθ : 1 < θ) (hK : 0 ≤ K)
    (hΞ_diag : ∀ s, Ξ s s = 0)
    (hf_cont : ContinuousOn f (Icc a b))
    (hab : a ≤ b)
    (hω : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖sewingDefect Ξ s u t‖ ≤ K * ‖f t - f s‖ ^ (p * θ)) :
    ∃ ω : ℝ → ℝ → ℝ, SewingCondition Ξ ω θ K a b := by
  sorry -- Take ω(s,t) = ‖f(t) - f(s)‖^p. Then ω^θ = ‖f(t) - f(s)‖^(p·θ).
  -- Super-additivity of ω follows from the triangle inequality + concavity argument
  -- for p ≥ 1 (Minkowski-type).

end PVarSewing

/-! ### Application: Young integration as a sewing -/

section Young

/-- **Young integration via sewing**. For paths `X` of finite `p`-variation and `Y` of
finite `q`-variation with `1/p + 1/q > 1`, the Young integral `∫ Y dX` exists and
equals the sewn map of `Ξ(s, t) = Y(s) · (X(t) - X(s))`.

The defect is `δΞ(s, u, t) = (Y(s) - Y(u)) · (X(t) - X(u))`, bounded by
`‖Y‖_{q-var} · ‖X‖_{p-var} · ω(s,t)^(1/p + 1/q)`. Since `1/p + 1/q > 1`,
the sewing condition is satisfied with `θ = 1/p + 1/q > 1`.

This recovers the classical Young-Loève-Towghi theorem as a special case of
the Sewing Lemma. -/
theorem young_integral_exists [CompleteSpace E]
    {X Y : ℝ → ℝ} {p q : ℝ} {a b : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hab : a ≤ b)
    (hX : StochCalc.HasFinitePVariationOn p X (Icc a b))
    (hY : StochCalc.HasFinitePVariationOn q Y (Icc a b)) :
    ∃ I : ℝ → ℝ → ℝ,
      (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → I s t = I s u + I u t) ∧
      (∃ C, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
        |I s t - Y s * (X t - X s)| ≤ C) := by
  sorry -- Define Ξ(s,t) = Y(s) · (X(t) - X(s)).
  -- δΞ(s,u,t) = -(Y(u) - Y(s)) · (X(t) - X(u)).
  -- By Young's inequality for sums: ‖δΞ‖ ≤ ‖Y‖_{q-var} · ‖X‖_{p-var} · ω^θ
  -- with θ = 1/p + 1/q > 1. Apply the Sewing Lemma.

end Young
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end StochCalc
