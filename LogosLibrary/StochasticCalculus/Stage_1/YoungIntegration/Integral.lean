/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: YoungIntegration/Integral.lean
-/
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Def
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Properties
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Unique
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Regular
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Linear
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.ByParts
--import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Consistency
/-!
# The Young Integral

The **Young integral** `∫_s^t Y dX` for paths `X, Y` with complementary
regularity: `X` is `γ`-Hölder and `Y` is `δ`-Hölder with `γ + δ > 1`.

## Construction

The Young integral is *defined* as the Layer 2 sewn map applied to the
approximation `Ξ(s,t) = (X(t) - X(s)) • Y(s)`:

  `∫_s^t Y dX  :=  sewingMap₂ Ξ ω₁ ω₂ δ γ (C_X · C_Y) 1 1 a b`

Everything that follows — existence, uniqueness, additivity, the approximation
bound — is an *immediate corollary* of the Stage 0 infrastructure. No new
convergence arguments are needed.

## Main results

* `youngIntegral` — the integral itself (definition)
* `youngIntegral_approx` — the **Young–Loève estimate**:
    `‖∫_s^t Y dX - (X(t) - X(s)) • Y(s)‖ ≤ C_{γ,δ} · C_X · C_Y · |t-s|^{γ+δ}`
* `youngIntegral_additive` — additivity: `∫_s^t = ∫_s^u + ∫_u^t`
* `youngIntegral_diag` — vanishes on diagonal: `∫_s^s = 0`
* `youngIntegral_unique` — characterisation by approximation bound + additivity
* `youngIntegral_pvar` — the indefinite integral has finite `p`-variation

## Why Layer 2?

The defect `δΞ(s,u,t) = -(Y(u) - Y(s)) • (X(t) - X(u))` naturally separates
into a factor depending on `[s,u]` (with exponent `δ`) and a factor depending
on `[u,t]` (with exponent `γ`). These exponents are *different* whenever `X`
and `Y` have different regularity — which is the generic situation.

Layer 1 (with a single control `|t-s|^θ`) would force `θ = γ + δ`, which loses
the factorisation. Layer 2 preserves it, and this is essential for the refinement
cost bound and hence for additivity and general convergence.

## References

* [Young, L.C., *An inequality of the Hölder type*, Acta Math. **67** (1936)]
* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 1]
* [Lyons, T., *Differential equations driven by rough signals* (1998)]
-/
