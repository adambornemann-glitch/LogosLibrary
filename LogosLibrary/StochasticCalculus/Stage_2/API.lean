/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/API.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.Axioms.TensorLift
import LogosLibrary.StochasticCalculus.Stage_2.Integral.ItoLyons
/-!
# Stage 2 API — Rough Integration

Bundled interface for rough integration against a geometric rough path.

## What this file provides

1. **`RoughIntegralData`** — bundled structure packaging the integral with all properties
2. **`rough_integral`** — main constructor
3. **Unbundled theorems** — additivity, approximation, Hölder bound, closure
4. **`roughIntegral_closure`** — the integral of a controlled path is controlled
5. **`rough_integral_continuity`** — joint continuity in (𝐗, Y, Y')

## What Stage 3 needs

* **Closure**: the Picard map `Y ↦ ∫ f(Y) d𝐗` preserves the controlled path space
* **Hölder bound with explicit constants**: the contraction needs `C_output ≤ λ · C_input`
* **Continuity**: the Itô–Lyons estimate for uniqueness and stability of RDE solutions
* **Additivity**: inherited by the ODE solution from the integral

## References

* Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004)
* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapters 4, 8
-/

open NormedTensorSquare StochCalc.TruncTensor₂ StochCalc.GroupLike₂ Real
open StochCalc.RoughPath StochCalc.ControlledPath

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {γ C a b : ℝ}
variable {X : RoughPath V γ C a b}

/-! ### Bundled structure -/

/-- **Rough integral data**: packages the integral with all its properties.

The primary API object for Stage 3. -/
structure RoughIntegralData
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X) where
  /-- The integral: `I(s, t) = ∫_s^t Y d𝐗`. -/
  val : ℝ → ℝ → F
  /-- Vanishes on the diagonal. -/
  diag : ∀ s, a ≤ s → s ≤ b → val s s = 0
  /-- Additivity (Chasles property). -/
  additive : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    val s t = val s u + val u t
  /-- Approximation by the rough Taylor expansion. -/
  approx : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖val s t - roughApproxMap P cY s t‖ ≤
      roughSewingConst P cY * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ)
  /-- Hölder increment bound: `‖I(s,t)‖ ≤ C_I · |t-s|^γ`. -/
  increment : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖val s t‖ ≤
      (‖P.σ‖ * cY.M_Y * C +
       ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * (b - a) ^ γ +
       roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ)) *
        |t - s| ^ γ
  /-- The integral output is a controlled path (closure). -/
  controlled : ControlledPath F X

/-! ### Construction -/

/-- **The rough integral** (main API entry point).

Given a rough path `𝐗`, a controlled path `(Y, Y')`, and a compatible
pairing `P = (σ, τ)`, constructs `∫ Y d𝐗` with all properties.

Usage in Stage 3:
```
  let I := rough_integral P cY
  -- I.val s t           : the integral ∫_s^t Y d𝐗
  -- I.additive ...      : Chasles property
  -- I.approx ...        : 3γ-order approximation
  -- I.increment ...     : γ-Hölder bound
  -- I.controlled        : the output is a controlled path
``` -/
def rough_integral
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X) :
    RoughIntegralData P cY where
  val := roughIntegral P cY
  diag := fun _s has hsb => roughIntegral_diag P cY has hsb
  additive := fun _s _u _t has hsu hut htb =>
    roughIntegral_additive P cY has hsu hut htb
  approx := fun _s _t has hst htb =>
    roughIntegral_approx P cY has hst htb
  increment := fun _s _t has hst htb =>
    roughIntegral_increment_bound P cY has hst htb
  controlled :=
    roughIntegral_controlled P cY
      (fun _s _u _t has hsu hut htb =>
        roughIntegral_additive P cY has hsu hut htb)

/-! ### Unbundled convenience theorems -/

/-- Rough integral additivity (unbundled). -/
theorem rough_integral_additive'
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    (rough_integral P cY).val s t =
      (rough_integral P cY).val s u +
      (rough_integral P cY).val u t :=
  (rough_integral P cY).additive s u t has hsu hut htb

/-- Rough integral approximation (unbundled). -/
theorem rough_integral_approx'
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖(rough_integral P cY).val s t - roughApproxMap P cY s t‖ ≤
      roughSewingConst P cY * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) :=
  (rough_integral P cY).approx s t has hst htb

/-- Rough integral Hölder bound (unbundled). -/
theorem rough_integral_holder
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖(rough_integral P cY).val s t‖ ≤
      (‖P.σ‖ * cY.M_Y * C +
       ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * (b - a) ^ γ +
       roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ)) *
        |t - s| ^ γ :=
  (rough_integral P cY).increment s t has hst htb

/-- **The closure theorem** (unbundled): the rough integral of a controlled
path is itself controlled by `𝐗`.

This is the theorem that makes Picard iteration close:
- Gubinelli derivative: `Z'(s) = σ(Y(s), ·)`
- Remainder: `R^Z_{s,t} = ∫_s^t Y d𝐗 - σ(Y(s), X_{s,t})`
- Remainder regularity: `‖R^Z‖ ≤ C_Z · |t-s|^{2γ}` -/
def rough_integral_closure
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X) :
    ControlledPath F X :=
  (rough_integral P cY).controlled

/-! ### Joint continuity (Itô–Lyons) -/

/-- **Joint continuity estimate** for the rough integral.

The difference of two rough integrals is controlled by the distances
between the driving rough paths and between the controlled integrands.

This is the Itô–Lyons continuity theorem in its local form. Stage 3 uses
this for:
1. Uniqueness of RDE solutions (Lipschitz dependence on initial data)
2. Stability under smooth approximation (Wong–Zakai)
3. The contraction argument on small intervals -/
theorem rough_integral_continuity
    {C₁ C₂ : ℝ}
    {X₁ : RoughPath V γ C₁ a b}
    {X₂ : RoughPath V γ C₂ a b}
    (P : RoughIntegralPairing E V F)
    (cY₁ : ControlledPath E X₁)
    (cY₂ : ControlledPath E X₂)
    (dY : ControlledPathDist cY₁ cY₂)
    (dX : RoughPathDist X₁ X₂)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖roughIntegral P cY₁ s t - roughIntegral P cY₂ s t‖ ≤
      ((roughSewingConst P cY₁ + roughSewingConst P cY₂) *
          sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ) +
       ‖P.σ‖ * dY.D_path * C₁ +
       ‖P.σ‖ * cY₂.M_Y * dX.D₁ +
       ‖P.τ‖ * dY.D_deriv * ((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * (b - a) ^ γ +
       ‖P.τ‖ * cY₂.M_Y' * dX.D₂ * (b - a) ^ γ) *
        |t - s| ^ γ :=
  roughIntegral_continuity_estimate P cY₁ cY₂ dY dX
    (fun _s _u _t has hsu hut htb => roughIntegral_additive P cY₁ has hsu hut htb)
    (fun _s _u _t has hsu hut htb => roughIntegral_additive P cY₂ has hsu hut htb)
    has hst htb

/-! ### Summary of the Stage 2 → Stage 3 interface

Stage 3 imports this file and uses:
```
-- 1. Construct the integral
let I := rough_integral P cY

-- 2. Additivity
have := I.additive s u t has hsu hut htb

-- 3. Approximation (3γ-order)
have := I.approx s t has hst htb

-- 4. Hölder bound (γ-order)
have := I.increment s t has hst htb

-- 5. Closure: output is controlled (for Picard)
let cZ := rough_integral_closure P cY
-- cZ.Y' s = σ(Y(s), ·)          (Gubinelli derivative)
-- cZ.C_R = ...                    (explicit remainder constant)
-- cZ.R_bound ...                  (2γ-Hölder remainder)

-- 6. Continuity (Itô–Lyons): for uniqueness and stability
have := rough_integral_continuity P cY₁ cY₂ dY dX has hst htb

-- 7. Picard: Y ↦ ∫ f(Y) d𝐗 maps ControlledPath to ControlledPath
--    with controlled constants → contraction on small intervals
```
-/

end StochCalc
