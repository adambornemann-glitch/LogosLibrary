/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/Mass.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.DEP.Mass
namespace SpectralBridge.Bochner.BochnerExistence

open Complex MeasureTheory Filter Topology Set Real Function

variable {f : ℝ → ℂ}

/-! ## §4: Helly's selection theorem

This is the compactness engine. We need to extract a convergent subsequence
from the family of distribution functions associated to {μ_T}.

**Mathlib status**: Helly's selection theorem is likely NOT in Mathlib as of
early 2026. This section may require either:
- Proving Helly from scratch (substantial but self-contained)
- Using an alternative compactness argument
- Axiomatizing the selection principle

We take the Helly route: monotone + uniformly bounded ⟹ pointwise convergent
subsequence at a dense set ⟹ everywhere by right-continuity. -/

/-- The approximate distribution function:
    `F_T(x) = ∫_{-∞}^{x} Λ_T(ω) dω`.

This is monotone, right-continuous, bounded between 0 and f(0).re. -/
noncomputable def approxDistFn (f : ℝ → ℂ) (T : ℝ) (x : ℝ) : ℝ :=
  ∫ ω in Set.Iic x, approxDensityReal f T ω

/-- The approximate distribution function is monotone. -/
lemma approxDistFn_mono (hf : IsContinuous f) {T : ℝ} (hT : 0 < T) :
    Monotone (approxDistFn f T) := by
  sorry -- Monotonicity of integral over increasing sets, using Λ_T ≥ 0.

/-- The approximate distribution function is bounded by f(0).re. -/
lemma approxDistFn_le (hf : IsContinuous f) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    approxDistFn f T x ≤ (f 0).re := by
  sorry -- F_T(x) = ∫_{Iic x} Λ_T ≤ ∫_ℝ Λ_T = f(0).re

/-- The approximate distribution function is non-negative. -/
lemma approxDistFn_nonneg (hf : IsContinuous f) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    0 ≤ approxDistFn f T x := by
  sorry -- Integral of non-negative function over a set is non-negative.

/-- The approximate distribution function is right-continuous. -/
lemma approxDistFn_rightContinuous (hf : IsContinuous f) {T : ℝ} (hT : 0 < T) :
    ∀ x, ContinuousWithinAt (approxDistFn f T) (Set.Ici x) x := by
  sorry -- Continuity of ω ↦ ∫_{Iic x} Λ_T as x increases.
        -- Uses: Λ_T continuous, dominated convergence.

/-- **Helly's Selection Theorem** (for our setting).

Given a sequence of monotone, uniformly bounded, right-continuous functions
`F_n : ℝ → ℝ` with `0 ≤ F_n(x) ≤ M`, there exists a subsequence converging
pointwise to a monotone right-continuous function at all continuity points.

This is the main compactness tool. If it's not in Mathlib, it can be proved
via a diagonal argument over a countable dense set (the rationals). -/
theorem helly_selection
    {M : ℝ} (hM : 0 < M)
    (F : ℕ → ℝ → ℝ)
    (h_mono : ∀ n, Monotone (F n))
    (h_bound : ∀ n x, 0 ≤ F n x ∧ F n x ≤ M)
    (h_rc : ∀ n x, ContinuousWithinAt (F n) (Set.Ici x) x) :
    ∃ (φ : ℕ → ℕ) (G : ℝ → ℝ),
      StrictMono φ ∧
      Monotone G ∧
      (∀ x, 0 ≤ G x ∧ G x ≤ M) ∧
      (∀ x, ContinuousWithinAt G (Set.Ici x) x) ∧
      -- Pointwise convergence at continuity points of G
      (∀ x, ContinuousAt G x →
        Tendsto (fun n => F (φ n) x) atTop (𝓝 (G x))) := by
  sorry
  -- Proof sketch:
  --
  -- Step 1: Enumerate the rationals as {q_1, q_2, ...}.
  --
  -- Step 2: Diagonal argument. {F_n(q_1)} is bounded, so has a convergent
  --   subsequence. Within that, {F_{n_k}(q_2)} is bounded, extract again.
  --   Continue and take the diagonal subsequence φ.
  --
  -- Step 3: Define G(x) = inf_{q > x, q ∈ ℚ} lim_{n→∞} F(φ(n))(q).
  --   This is the right-continuous regularization of the pointwise limit.
  --
  -- Step 4: G is monotone and right-continuous by construction.
  --
  -- Step 5: At continuity points of G, F(φ(n))(x) → G(x).
  --
  -- Lean challenge: the diagonal extraction and the interplay between
  -- rationals and reals requires careful filter/sequence management.
  -- Total estimated effort: ~500 lines.

end SpectralBridge.Bochner.BochnerExistence
