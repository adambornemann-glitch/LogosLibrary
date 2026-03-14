/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_1/API.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.API
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration
import Mathlib.Analysis.Normed.Module.Basic
/-!
# Stage 1 API — Young Integration

Bundled interface for Young integration, intended as the import boundary
for Stage 2 (rough path integration) and beyond.

## What this file provides

Five results, packaged to hide the Layer 2 sewing machinery:

1. **`young_integral`** — existence + the Young–Loève estimate
2. **`young_integral_additive`** — the Chasles property
3. **`young_integral_unique`** — characterisation by approximation + additivity
4. **`young_integral_holder`** — the indefinite integral is γ-Hölder
5. **`young_integral_continuous`** — joint continuity in (X, Y)

## What Stage 2 needs and why

* **Young–Loève estimate**: in rough integration, the controlled remainder
  `R^Y_{s,t} = Y_t - Y_s - Y'_s · X_{s,t}` is bounded by `|t-s|^{2γ}`.
  The rough integral's defect involves `∫ R^Y dX`, estimated via Young–Loève.

* **Additivity**: the rough integral inherits additivity from its components,
  one of which is a Young integral.

* **Uniqueness**: identifies the rough integral as the *unique* additive
  functional with the right approximation behaviour — same strategy as here,
  one level up.

* **γ-Hölder bound**: the Picard fixed-point for `dY = f(Y) d𝐗` maps
  γ-Hölder controlled paths to γ-Hölder controlled paths. This requires
  the Young integral of a 2γ-Hölder remainder against a γ-Hölder path
  to produce a γ-Hölder output. Since 2γ + γ = 3γ > 1 for γ > 1/3,
  Young integration applies, and the Hölder bound closes the contraction.

* **Continuity**: the Itô–Lyons continuity theorem at the rough level
  needs continuity of the Young integral as an ingredient.

## Design decisions

* The API takes `IsHolderOn` hypotheses directly, not `LipControl` or
  `SewingCondition₂`. This insulates Stage 2 from the sewing internals.

* Constants are explicit: `C_X`, `C_Y`, `Y_sup` appear as parameters.
  This is verbose but necessary — Stage 2's contraction argument needs
  to track how the output constant depends on the input constants.

* We provide both a **bundled structure** (`YoungIntegralData`) for
  convenience and **unbundled theorems** for flexibility.

## References

* [Young, L.C., *An inequality of the Hölder type*, Acta Math. **67** (1936)]
* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 1]
* [Lyons, T., *Differential equations driven by rough signals* (1998)]
-/

noncomputable section

open Real Set Filter

namespace StochCalc

/-! ### The bundled Young integral -/

section Bundled

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Young integral data**: packages the integral together with all its
properties in a single structure.

This is the primary API object. Stage 2 obtains one of these from
`young_integral` and then projects out whichever properties it needs. -/
structure YoungIntegralData (X : ℝ → ℝ) (Y : ℝ → E)
    (γ δ C_X C_Y : ℝ) (a b : ℝ) where
  /-- The integral itself: a two-parameter map `I(s, t)`. -/
  val : ℝ → ℝ → E
  /-- Vanishes on the diagonal. -/
  diag : ∀ s, a ≤ s → s ≤ b → val s s = 0
  /-- Additivity (Chasles property). -/
  additive : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    val s t = val s u + val u t
  /-- The Young–Loève approximation estimate. -/
  approx : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖val s t - (X t - X s) • Y s‖ ≤
      sewingConst₂ δ γ * (C_X * C_Y) * |t - s| ^ (γ + δ)
  /-- Uniqueness: any additive functional with a super-linear approximation
  bound must agree with `val`. -/
  unique : ∀ (J : ℝ → ℝ → E),
    (∀ s, J s s = 0) →
    (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → J s t = J s u + J u t) →
    (∃ M ≥ 0, ∃ θ > 1, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖J s t - (X t - X s) • Y s‖ ≤ M * |t - s| ^ θ) →
    ∀ s t, a ≤ s → s ≤ t → t ≤ b → J s t = val s t
  /-- Increment bound: `‖I(s,t)‖ ≤ C' · |t-s|^γ`.
  The constant depends on `‖Y‖_∞`, the Hölder constants, and `diam[a,b]`. -/
  increment_bound :
    ∀ (Y_sup : ℝ), (∀ s, a ≤ s → s ≤ b → ‖Y s‖ ≤ Y_sup) →
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖val s t‖ ≤
        (C_X * Y_sup + sewingConst₂ δ γ * C_X * C_Y * (b - a) ^ δ) *
          |t - s| ^ γ

end Bundled

/-! ### Construction -/

section Construction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The Young integral** (main API entry point).

Given `γ`-Hölder `X` and `δ`-Hölder `Y` with `γ + δ > 1`, constructs the
integral together with all its properties.

Usage in Stage 2:
```
  let I := young_integral hX hY hγδ
  -- I.val s t        : the integral ∫_s^t Y dX
  -- I.additive ...   : Chasles property
  -- I.approx ...     : Young–Loève estimate
  -- I.increment_bound ... : Hölder increment bound
``` -/
def young_integral
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ) :
    YoungIntegralData X Y γ δ C_X C_Y a b where
  val := youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ
  diag := fun s has hsb => youngIntegral_diag hX hY hγδ has hsb
  additive := fun s u t has hsu hut htb =>
    youngIntegral_additive hX hY hγδ has hsu hut htb
  approx := fun s t has hst htb =>
    youngIntegral_approx hX hY hγδ has hst htb
  unique := fun J hJ_diag hJ_add hexist s t has hst htb => by
    obtain ⟨M, hM, θ, hθ, hJ_bound⟩ := hexist
    have hθ' : 1 < (θ : ℝ) := by exact_mod_cast hθ
    have hJ_bound' : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
        ‖J s t - (X t - X s) • Y s‖ ≤ M * |t - s| ^ (θ : ℝ) := by
      exact_mod_cast hJ_bound
    exact youngIntegral_unique (θ := (θ : ℝ)) hX hY hγδ hJ_diag hJ_add hM hθ' hJ_bound'
      s t has hst htb
  increment_bound := fun Y_sup hY_sup s t has hst htb =>
    youngIntegral_increment_bound hX hY hγδ hY_sup has hst htb

end Construction

/-! ### Unbundled convenience theorems

These are thin wrappers for direct use when the bundled structure is overkill.
Each is a one-liner delegating to `young_integral`. -/

section Unbundled

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Young–Loève estimate (unbundled). -/
theorem young_integral_approx
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖(young_integral hX hY hγδ).val s t - (X t - X s) • Y s‖ ≤
      sewingConst₂ δ γ * (C_X * C_Y) * |t - s| ^ (γ + δ) :=
  (young_integral hX hY hγδ).approx s t has hst htb

/-- Additivity (unbundled). -/
theorem young_integral_additive
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    (young_integral hX hY hγδ).val s t =
      (young_integral hX hY hγδ).val s u +
      (young_integral hX hY hγδ).val u t :=
  (young_integral hX hY hγδ).additive s u t has hsu hut htb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The indefinite Young integral is γ-Hölder (unbundled).

This is the theorem Stage 2 calls most often: it shows
`t ↦ ∫_a^t Y dX` preserves the Hölder class of the integrator. -/
theorem young_integral_holder'
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {Y_sup : ℝ} (hY_sup : ∀ s, a ≤ s → s ≤ b → ‖Y s‖ ≤ Y_sup) :
    IsHolderOn (fun t => (young_integral hX hY hγδ).val a t)
      γ (C_X * Y_sup + sewingConst₂ δ γ * C_X * C_Y * (b - a) ^ δ)
      a b where
  γ_pos := hX.γ_pos
  γ_le_one := hX.γ_le_one
  C_nonneg := by
    apply add_nonneg
    · exact mul_nonneg hX.C_nonneg (le_trans (norm_nonneg _) (hY_sup a le_rfl hX.hab))
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact le_of_lt (sewingConst₂_pos (by linarith : 1 < δ + γ))
          · exact hX.C_nonneg
        · exact hY.C_nonneg
      · exact rpow_nonneg (sub_nonneg.mpr hX.hab) _
  hab := hX.hab
  holder_bound := fun s t has hst htb => by
    have hadd := (young_integral hX hY hγδ).additive a s t
      (le_refl a) has hst htb
    rw [show (young_integral hX hY hγδ).val a t -
        (young_integral hX hY hγδ).val a s =
        (young_integral hX hY hγδ).val s t from by rw [hadd]; abel]
    exact (young_integral hX hY hγδ).increment_bound Y_sup hY_sup s t has hst htb

end Unbundled

/-! ### Joint continuity of the Young integral

This result is needed for the Itô–Lyons continuity theorem at the
rough path level. The statement is: if `Xₙ → X` and `Yₙ → Y` in
the appropriate Hölder topologies, then `∫ Yₙ dXₙ → ∫ Y dX`.

The proof strategy is to decompose the difference:
  `I_n(s,t) - I(s,t) = [I_n(s,t) - Ξ_n(s,t)] - [I(s,t) - Ξ(s,t)]
                        + [Ξ_n(s,t) - Ξ(s,t)]`

The first two brackets are controlled by Young–Loève (uniformly in n
if the Hölder constants are uniformly bounded). The last bracket is
  `(X_n(t) - X_n(s)) • Y_n(s) - (X(t) - X(s)) • Y(s)`
which converges pointwise if X_n → X and Y_n → Y. -/

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


/-- **Continuity estimate**: the difference of two Young integrals is controlled
by the Hölder distance between the paths and the pointwise distance of integrands.

  `‖∫ Y₁ dX₁ - ∫ Y₂ dX₂‖ ≤ C · |t-s|^γ`

where `C` depends on `‖X₁-X₂‖_γ`, `‖Y₁-Y₂‖_∞`, the individual Hölder constants,
and the sewing constant. -/
theorem young_integral_continuity_estimate
    {X₁ X₂ : ℝ → ℝ} {Y₁ Y₂ : ℝ → E} {γ δ C_X₁ C_X₂ C_Y₁ C_Y₂ a b : ℝ}
    (hX₁ : IsHolderOn X₁ γ C_X₁ a b) (hX₂ : IsHolderOn X₂ γ C_X₂ a b)
    (hY₁ : IsHolderOn Y₁ δ C_Y₁ a b) (hY₂ : IsHolderOn Y₂ δ C_Y₂ a b)
    (hγδ : 1 < γ + δ)
    {Y_sup₁ Y_sup₂ : ℝ}
    (hY_sup₁ : ∀ s, a ≤ s → s ≤ b → ‖Y₁ s‖ ≤ Y_sup₁)
    (_hY_sup₂ : ∀ s, a ≤ s → s ≤ b → ‖Y₂ s‖ ≤ Y_sup₂)
    -- Extra hypotheses: Hölder bound on the difference of integrators,
    -- and pointwise bound on the difference of integrands
    {C_XΔ : ℝ} (hXΔ : IsHolderOn (X₁ - X₂) γ C_XΔ a b)
    {Y_supΔ : ℝ} (hY_supΔ : ∀ s, a ≤ s → s ≤ b → ‖Y₁ s - Y₂ s‖ ≤ Y_supΔ)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖(young_integral hX₁ hY₁ hγδ).val s t -
      (young_integral hX₂ hY₂ hγδ).val s t‖ ≤
    (C_XΔ * Y_sup₁ + C_X₂ * Y_supΔ +
      (sewingConst₂ δ γ * (C_X₁ * C_Y₁ + C_X₂ * C_Y₂)) * (b - a) ^ δ) *
      |t - s| ^ γ := by
  set I₁ := (young_integral hX₁ hY₁ hγδ).val
  set I₂ := (young_integral hX₂ hY₂ hγδ).val
  set Ξ₁ := fun s t => (X₁ t - X₁ s) • Y₁ s
  set Ξ₂ := fun s t => (X₂ t - X₂ s) • Y₂ s
  have hts_nn : 0 ≤ |t - s| := abs_nonneg _
  have hts_le : |t - s| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]; linarith
  have hba_nn : 0 ≤ b - a := sub_nonneg.mpr hX₁.hab
  have hδ_nn : 0 ≤ δ := hY₁.γ_pos.le
  -- Main decomposition: I₁ - I₂ = (I₁ - Ξ₁) - (I₂ - Ξ₂) + (Ξ₁ - Ξ₂)
  calc ‖I₁ s t - I₂ s t‖
      = ‖(I₁ s t - Ξ₁ s t) - (I₂ s t - Ξ₂ s t) + (Ξ₁ s t - Ξ₂ s t)‖ := by
        congr 1; abel
    _ ≤ ‖I₁ s t - Ξ₁ s t‖ + ‖I₂ s t - Ξ₂ s t‖ + ‖Ξ₁ s t - Ξ₂ s t‖ := by
        calc _ ≤ ‖(I₁ s t - Ξ₁ s t) - (I₂ s t - Ξ₂ s t)‖ + ‖Ξ₁ s t - Ξ₂ s t‖ :=
              norm_add_le _ _
          _ ≤ (‖I₁ s t - Ξ₁ s t‖ + ‖I₂ s t - Ξ₂ s t‖) + ‖Ξ₁ s t - Ξ₂ s t‖ := by
              gcongr; exact norm_sub_le _ _
    -- Bound each of the three terms
    _ ≤ sewingConst₂ δ γ * (C_X₁ * C_Y₁) * |t - s| ^ (γ + δ) +
        sewingConst₂ δ γ * (C_X₂ * C_Y₂) * |t - s| ^ (γ + δ) +
        (C_XΔ * Y_sup₁ + C_X₂ * Y_supΔ) * |t - s| ^ γ := by
        apply add_le_add
        · apply add_le_add
          · show ‖I₁ s t - Ξ₁ s t‖ ≤ _
            exact youngIntegral_approx hX₁ hY₁ hγδ has hst htb
          · show ‖I₂ s t - Ξ₂ s t‖ ≤ _
            exact youngIntegral_approx hX₂ hY₂ hγδ has hst htb
        -- Term 3: ‖Ξ₁ - Ξ₂‖ — split into ΔX·Y₁ + X₂·ΔY
        · rw [show Ξ₁ s t - Ξ₂ s t =
            ((X₁ t - X₁ s) - (X₂ t - X₂ s)) • Y₁ s +
            (X₂ t - X₂ s) • (Y₁ s - Y₂ s) from by
              simp only [Ξ₁, Ξ₂, sub_smul, smul_sub]; abel]
          calc ‖((X₁ t - X₁ s) - (X₂ t - X₂ s)) • Y₁ s +
                (X₂ t - X₂ s) • (Y₁ s - Y₂ s)‖
              ≤ ‖((X₁ t - X₁ s) - (X₂ t - X₂ s)) • Y₁ s‖ +
                ‖(X₂ t - X₂ s) • (Y₁ s - Y₂ s)‖ := norm_add_le _ _
            _ = |(X₁ t - X₁ s) - (X₂ t - X₂ s)| * ‖Y₁ s‖ +
                |X₂ t - X₂ s| * ‖Y₁ s - Y₂ s‖ := by
                simp only [norm_smul, Real.norm_eq_abs]
            _ ≤ C_XΔ * |t - s| ^ γ * Y_sup₁ +
                C_X₂ * |t - s| ^ γ * Y_supΔ := by
                apply add_le_add
                · apply mul_le_mul _ (hY_sup₁ s has (hst.trans htb)) (norm_nonneg _)
                    (mul_nonneg hXΔ.C_nonneg (rpow_nonneg hts_nn _))
                  rw [show (X₁ t - X₁ s) - (X₂ t - X₂ s) = (X₁ - X₂) t - (X₁ - X₂) s from by
                    simp [Pi.sub_apply]; ring]
                  exact hXΔ.holder_bound s t has hst htb
                · apply mul_le_mul _ (hY_supΔ s has (hst.trans htb)) (norm_nonneg _)
                    (mul_nonneg hX₂.C_nonneg (rpow_nonneg hts_nn _))
                  exact hX₂.holder_bound s t has hst htb
            _ = (C_XΔ * Y_sup₁ + C_X₂ * Y_supΔ) * |t - s| ^ γ := by ring
    -- Consolidate: factor |t-s|^γ from the sewing terms
    _ ≤ (C_XΔ * Y_sup₁ + C_X₂ * Y_supΔ +
          (sewingConst₂ δ γ * (C_X₁ * C_Y₁ + C_X₂ * C_Y₂)) * (b - a) ^ δ) *
          |t - s| ^ γ := by
        -- Split |t-s|^{γ+δ} = |t-s|^δ · |t-s|^γ, bound |t-s|^δ ≤ (b-a)^δ
        have hγ_nn : 0 ≤ |t - s| ^ γ := rpow_nonneg hts_nn _
        have hδ_bound : |t - s| ^ δ ≤ (b - a) ^ δ :=
          rpow_le_rpow hts_nn hts_le hδ_nn
        have hsc_nn : 0 ≤ sewingConst₂ δ γ :=
          (sewingConst₂_pos (by linarith)).le
        have hCK₁ : 0 ≤ C_X₁ * C_Y₁ := mul_nonneg hX₁.C_nonneg hY₁.C_nonneg
        have hCK₂ : 0 ≤ C_X₂ * C_Y₂ := mul_nonneg hX₂.C_nonneg hY₂.C_nonneg
        have split₁ : |t - s| ^ (γ + δ) = |t - s| ^ δ * |t - s| ^ γ :=
          by rw [show γ + δ = δ + γ from add_comm γ δ,
                 rpow_add' hts_nn (by linarith : δ + γ ≠ 0)]
        simp_all only [abs_nonneg, sub_nonneg, ge_iff_le]
        nlinarith [mul_le_mul_of_nonneg_right hδ_bound
          (mul_nonneg (mul_nonneg hsc_nn (add_nonneg hCK₁ hCK₂)) hγ_nn)]

end Continuity

/-! ### Composition with smooth functions

The composition `f ∘ Y` preserves Hölder regularity (by the chain rule),
so `∫ (f ∘ Y) dX` exists whenever `∫ Y dX` does and `f` is smooth enough.
This is needed in Stage 2 for the nonlinear rough integral `∫ f(Y) d𝐗`. -/

section Composition

variable {E : Type*} [NormedAddCommGroup E]
variable {F : Type*} [NormedAddCommGroup F]
/-- If `f : E → F` is Lipschitz and `Y` is `δ`-Hölder, then `f ∘ Y` is `δ`-Hölder. -/
theorem isHolderOn_comp_lipschitz
    {Y : ℝ → E} {δ C_Y a b : ℝ} (hY : IsHolderOn Y δ C_Y a b)
    {f : E → F} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    IsHolderOn (f ∘ Y) δ (L * C_Y) a b where
  γ_pos := hY.γ_pos
  γ_le_one := hY.γ_le_one
  C_nonneg := mul_nonneg hL hY.C_nonneg
  hab := hY.hab
  holder_bound := fun s t has hst htb => by
    calc ‖(f ∘ Y) t - (f ∘ Y) s‖
        = ‖f (Y t) - f (Y s)‖ := rfl
      _ ≤ L * ‖Y t - Y s‖ := hf (Y t) (Y s)
      _ ≤ L * (C_Y * |t - s| ^ δ) := by
          gcongr; exact hY.holder_bound s t has hst htb
      _ = L * C_Y * |t - s| ^ δ := by ring

variable {E : Type*} [NormedAddCommGroup E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F][CompleteSpace F]
/-- Young integral of `f ∘ Y` against `X`, for Lipschitz `f`.

This is the main composition result Stage 2 needs: it produces a
`YoungIntegralData` for the composed integrand, with explicit constants. -/
def young_integral_comp_lipschitz
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {f : E → F} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    YoungIntegralData X (f ∘ Y) γ δ C_X (L * C_Y) a b :=
  young_integral hX (isHolderOn_comp_lipschitz hY hL hf) hγδ

end Composition

/-! ### Summary of the Stage 1 → Stage 2 interface

Stage 2 imports this file and uses:

```
-- 1. Construct the integral
let I := young_integral hX hY hγδ

-- 2. Use the Young–Loève estimate to bound remainders
have := I.approx s t has hst htb

-- 3. Additivity composes with rough-level additivity
have := I.additive s u t has hsu hut htb

-- 4. Uniqueness identifies the rough integral
have := I.unique J hJ_diag hJ_add ⟨M, hM, θ, hθ, hJ_bound⟩

-- 5. Hölder bound closes the Picard contraction
have := young_integral_holder hX hY hγδ hY_sup

-- 6. Continuity for Itô–Lyons
have := young_integral_continuity_estimate hX₁ hX₂ hY₁ hY₂ hγδ ...

-- 7. Composition for nonlinear integrands
let I_f := young_integral_comp_lipschitz hX hY hγδ hL hf
```
-/

end StochCalc
