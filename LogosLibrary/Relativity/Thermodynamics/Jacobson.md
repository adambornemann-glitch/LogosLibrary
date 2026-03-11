# Jacobson.lean

## Disclaimer

All errors and misinterpretations are solely the responsibility of the author (Adam Bornemann). This is an independent project. It has not been reviewed or endorsed by Ted Jacobson, Alain Connes, Carlo Rovelli, or any other physicist or mathematician whose work is referenced.

## Overview

This file formalizes the thermodynamic foundations of Ted Jacobson's 1995 derivation of the Einstein equation from the Clausius relation δQ = TdS applied to local Rindler horizons.

The main contribution is a careful treatment of **which temperature** appears in that relation — a subtlety that is often glossed over and leads to confusion about relativistic temperature transformation.

---

## The 1995 Argument (Informal)

Jacobson's insight: take any point in spacetime. An accelerating observer there perceives a local Rindler horizon with an associated temperature. Demand that the Clausius relation δQ = TdS holds for energy flux across this horizon. The requirement that this work *at every point* forces the spacetime geometry to satisfy the Einstein equation.

The Einstein equation is thus an *equation of state* — a thermodynamic consistency condition — rather than a fundamental dynamical law. As Jacobson put it: it may be no more appropriate to quantize the Einstein equation than to quantize the wave equation for sound in air.

---

## The Temperature Hierarchy

The formalization distinguishes two temperatures that are often conflated:

**T_boost = ℏ/2π** (§1)

The "boost temperature." This is the temperature of the Minkowski vacuum with respect to the boost Hamiltonian H_B. The Bisognano-Wichmann theorem says the vacuum restricted to a Rindler wedge is the Gibbs state ρ = Z⁻¹ exp(-2πH_B/ℏ).

Crucially, H_B generates translations of *hyperbolic angle* — a dimensionless parameter — not proper time. T_boost is modular-intrinsic: it comes from the algebraic structure of the vacuum state alone, with no reference to any particular observer's acceleration.

**T_U = ℏa/2π = a · T_boost** (§2)

The Unruh temperature for an observer with proper acceleration a. This is what an accelerating detector actually clicks at. It parameterizes *proper time* along a specific worldline, which requires knowing the acceleration a as external data.

The factorization T_U = a · T_boost makes the relationship explicit. At unit acceleration they coincide, which is why the distinction often goes unnoticed.

**Why it matters for Jacobson 1995:**

The temperature in δQ = TdS is T_boost, not T_U. The derivation uses the boost Killing vector χ^a on the local Rindler horizon, with heat flux defined as boost energy. The Clausius relation at T_boost is what yields the Einstein equation — and T_boost is the same (ℏ/2π) for all local horizons, independent of any observer's acceleration.

This universality is essential. If T_U appeared instead, the argument would depend on which accelerated observer you imagine, and different accelerations would give different equations.

---

## The Two-Thermometer Resolution (§5)

A puzzle: consider two uniformly accelerated observers A and B, both with proper acceleration a, but with relative velocity v between them. Each measures their own Unruh temperature. Both get T_U = a/(2π).

Same temperature, despite nonzero γ. If Ott's transformation (T → γT) applied, shouldn't one observer see the other's bath as hotter?

**Resolution:** Ott governs *external* observations — measuring a thermal system you're boosted relative to. The Unruh effect is *intrinsic* — each observer's own horizon produces a thermal bath coupled only to that observer's detector.

A and B are measuring *different systems* (their own respective Rindler wedges), not the same system from different frames. Ott's scope conditions aren't met. The equal temperatures are expected, not paradoxical.

The formalization makes this precise with a type-level distinction between `ThermalSource.intrinsic` and `ThermalSource.external`, proving that Jacobson's scenario involves only intrinsic measurements where Ott doesn't apply.

---

## What's Formalized

**§1–2: Temperature definitions**
- `boostTemp : ℝ := 1 / (2 * π)` — the modular-intrinsic temperature
- `unruhTemp (a : ℝ) : ℝ := a / (2 * π)` — the observer-dependent temperature  
- `unruhTemp_eq_a_mul_boost` — the factorization T_U = a · T_boost

**§3–4: Thermal time structure**
- `BWThermalTimeMap` — the relation t = τ/(2πT) between modular parameter and physical time
- `jacobson_consistency` — the two routes to physical time (via T_boost or via acceleration) agree

**§5: Two-thermometer resolution**
- `TwoThermometers` — the scenario with two accelerated observers
- `ThermalSource` — intrinsic vs external measurements
- `jacobson_consistent` — both measure the same temperature, Ott doesn't apply, no contradiction

---

## References

- Jacobson, "Thermodynamics of Spacetime: The Einstein Equation of State," Phys. Rev. Lett. 75, 1260 (1995) — [arXiv:gr-qc/9504004](https://arxiv.org/abs/gr-qc/9504004)

- Jacobson, "Entanglement Equilibrium and the Einstein Equation," Phys. Rev. Lett. 116, 201101 (2016) — [arXiv:1505.04753](https://arxiv.org/abs/1505.04753)

- Eling, Guedens & Jacobson, "Non-equilibrium Thermodynamics of Spacetime," Phys. Rev. Lett. 96, 121301 (2006)

- Bisognano & Wichmann, "On the Duality Condition for Quantum Fields," J. Math. Phys. 17, 303 (1976)

- Unruh, "Notes on black-hole evaporation," Phys. Rev. D 14, 870 (1976)