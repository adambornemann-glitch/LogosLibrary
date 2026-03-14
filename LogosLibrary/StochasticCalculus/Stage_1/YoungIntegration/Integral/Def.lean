/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: YoungIntegration/Integral/Def.lean
-/
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Defect
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.PVarCont
import Mathlib.Analysis.Normed.Module.Basic

noncomputable section

open Real Set Filter Finset

namespace StochCalc

/-! ### Definition of the Young integral -/

section Definition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The Young integral** of `Y` against `X` on `[s, t]`.

Given `γ`-Hölder `X : ℝ → ℝ` and `δ`-Hölder `Y : ℝ → E` with `γ + δ > 1`,
this is the unique additive functional approximated by left-point Riemann sums.

Defined as the Layer 2 sewn map with:
  * `Ξ(s,t) = (X(t) - X(s)) • Y(s)`   (approximation map)
  * `ω₁ = ω₂ = |t - s|`               (absolute-value controls)
  * `α = δ, β = γ`                     (Hölder exponents)
  * `K = C_X · C_Y`                    (product of Hölder constants) -/
def youngIntegral (X : ℝ → ℝ) (Y : ℝ → E) (γ δ C_X C_Y a b : ℝ)
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    (s t : ℝ) : E :=
  sewingMap₂ (youngApprox X Y)
    (fun s t => |t - s|) (fun s t => |t - s|)
    δ γ (C_X * C_Y) 1 1 a b
    (youngApprox_sewingCondition₂ hX hY hγδ) s t

-- subscript-style with a pipe delimiter
local notation "∫[" X ", " Y " | " s ", " t "]" => youngIntegral X Y _ _ _ _ _ _ _ _ s t

end Definition

end StochCalc
