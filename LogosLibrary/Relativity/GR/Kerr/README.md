# The Kerr Metric in Lean: Ring Singularity Resolution via Finite Complexity

> *"Computer scientists fix bugs, while we ignore them."*

This library formalises the geometry, thermodynamics, and information-theoretic
structure of Kerr black holes in Lean 4, culminating in a precise statement:
**the ring "singularity" of a rotating black hole is finite in every
physically measurable quantity** — proper time to reach it, temperature, and
computational complexity. Only the coordinate-dependent curvature diverges.

The thesis, due to Adam Bornemann, is that the ring is better understood as a
**cold geometric boundary** analogous to the event horizon, rather than a place
where physics breaks down. The formalisation makes the logical dependencies of
this argument completely explicit.

## The Argument

The standard story goes: inside a rotating black hole, there is a ring at
r = 0, θ = π/2 where the Kretschner curvature scalar blows up, and therefore
Somebody Should Worry. Sixty years of worrying has produced remarkably little
clarity on what, exactly, is supposed to happen there.

This library takes a different approach:

1. **Locate the ring precisely.** It sits where Σ = r² + a²cos²θ vanishes —
   which requires *both* r = 0 and θ = π/2. In Schwarzschild (a = 0), this
   degenerates to a point. In Kerr (a ≠ 0), it traces out a ring of radius a.

2. **Prove the ring is not a Killing horizon.** At the horizons, Δ = 0 and
   Σ ≠ 0. At the ring, the situation is precisely reversed: Σ = 0 and
   Δ = a² ≠ 0. This means you cannot compute a surface gravity or temperature
   for the ring using standard Killing horizon machinery. Its temperature must
   come from *thermodynamics*, not geometry.

3. **Derive the ring temperature from thermal equilibrium.** In a steady-state
   black hole, no energy accumulates. The ring absorbs radiation from the outer
   horizon. Therefore, by the zeroth law, the ring equilibrates with the outer
   horizon: T_ring = T_Hawking. Not T_inner — the ring talks to the exterior,
   not to the Cauchy horizon.

4. **Show proper time to the ring is finite.** For Schwarzschild, the exact
   integral gives τ = πM (about 15 microseconds for a solar-mass black hole).
   For Kerr, the integral involves hypergeometric functions but remains O(M)
   for all spin parameters 0 ≤ |a| ≤ M.

5. **Define complexity and show it is finite at the ring.** Using
   C = 2μτ/π (from information-theoretic arguments), the complexity stored at
   the ring is C ~ O(μM) — finite, bounded, and well-behaved.

6. **Compare the ring with the horizon.** The ring has the same temperature as
   the outer horizon, is reachable in finite proper time, and stores finite
   complexity. The *only* thing that diverges is the Kretschner scalar, which
   is a coordinate-dependent quantity. The analogy with a coordinate singularity
   at the North Pole (where longitude becomes meaningless but nothing physical
   happens) is made explicit.

## File Structure

```
   Metric.lean
       │
       ▼
 Singularity.lean
       │
       ▼
Thermodynamics.lean
       │
       ├──────────────┐
       ▼              ▼
 Complexity.lean  Extensions.lean
```

### `Metric.lean`

The foundation. Defines the complete Kerr geometry in Boyer-Lindquist
coordinates:

- `KerrParams`: mass M > 0, spin parameter a with |a| ≤ M (subextremal)
- `BoyerLindquistCoords`: the coordinate chart with r > 0, 0 < θ < π
- `Sigma_K`, `Delta_K`, `rho_sq`: the three key metric functions
- `kerrMetric`: the full metric tensor g_μν v^μ w^ν
- `r_plus`, `r_minus`: outer and inner horizon radii
- `r_ergosphere`, `frameDraggingOmega`: ergosphere geometry

Key results include the Schwarzschild limit (a = 0 recovers the familiar
non-rotating case), the proof that Δ vanishes at both horizons (with an
explicitly computed factorisation), and the theorem that inside the ergosphere,
the frame-dragging angular velocity is nonzero — spacetime *itself* rotates
and all observers must co-rotate. The ergosphere proof that g_tt > 0 inside
the static limit is carried out in full, including the careful case split on
the sign of Δ.

### `Singularity.lean`

Locates the ring and establishes its geometric nature:

- `ring_singularity_characterization`: Σ = 0 iff r = 0 ∧ θ = π/2 (for a ≠ 0)
- `ring_not_horizon`: at the ring, Δ = a² ≠ 0
- `ring_no_geometric_temperature`: horizons have Δ = 0, the ring does not

The characterisation proof is surprisingly fiddly — you need to show that
cos θ = 0 within the range (0, π) forces θ = π/2, which requires chasing
through the integer parametrisation of arccos and showing the only valid
solution has k = 0. This is exactly the kind of detail that disappears in a
textbook proof ("clearly cos θ = 0 implies θ = π/2") but that Lean rightly
insists you justify.

### `Thermodynamics.lean`

Defines the thermal structure of Kerr black holes:

- `surface_gravity_outer`, `surface_gravity_inner`: κ at both horizons
- `hawkingTemperature`, `innerHorizonTemperature`: T = κ/(2π)
- `hawking_temperature_positive`: T_+ > 0 for strictly subextremal holes
- `horizon_temperatures_differ`: T_+ ≠ T_- (the two horizons radiate
  at different temperatures)
- `thermal_equilibrium_principle` (axiom): objects in steady-state equilibrium
  inside the hole adopt the outer horizon temperature
- `ring_temperature_equals_outer_horizon`: T_ring = T_Hawking
- `ring_thermally_coupled_to_outer_horizon`: the combined result

The proof that T_+ ≠ T_- is satisfying: it reduces to showing that r_+² ≠ r_-²
(since the numerator is the same but the denominators differ), which follows
from r_+ > r_- > 0 for strictly subextremal black holes. The field_simp
endgame is where the real work happens.

### `Complexity.lean`

The main result. Defines geodesic motion, proper time, and complexity:

- `schwarzschildProperTimeIntegral`: the integral ∫ r/√(r(2M-r)) dr
- `properTimeToRing`: finite proper time for both Schwarzschild and Kerr
- `complexity`: C = 2μτ/π
- `schwarzschild_complexity_exact`: C = 2μM for Schwarzschild
- `kerr_complexity_finite`: C is finite and positive for all Kerr
- `complexity_order_of_magnitude`: C ≤ O(μM), bounded by 20μM
- `ring_singularity_resolved`: τ finite ∧ C finite — the resolution
- `ring_like_horizon`: same T, finite C, finite τ — the comparison table

The Schwarzschild proper time integral τ = πM is stated as an axiom (the
substitution r = M(1 - cos θ) is a standard textbook calculation; formalising
it would require integration theory that is not the point of this library).

### `Extensions.lean`

Extensions and additional structure:

- `horizon_area`, `horizon_area_positive`: A = 4π(r_+² + a²) > 0
- `schwarzschild_area`: A = 16πM² in the non-rotating limit
- Extremal Kerr (|a| = M): horizons merge, T → 0, area → 8πM²
- Cauchy horizon instability (axiom): the interior is not described by the
  vacuum Kerr metric below the inner horizon
- **The Quintet Equation**: E = mc² combined with Landauer's principle
  E = IkT ln(2), giving mc² = IkT ln(2) — information has mass
- `information_has_mass`: for I > 0, T > 0, the equivalent mass is positive
- `black_hole_information_massive`: the Bekenstein-Hawking information content
  of a subextremal Kerr hole has positive equivalent mass

## Axioms

The library introduces the following physical axioms beyond Lean/Mathlib:

| Axiom | Role |
|-------|------|
| `schwarzschild_proper_time_integral_value` | τ = πM (textbook integral) |
| `kerr_proper_time_finite'` | τ is finite for all Kerr parameters |
| `proper_time_scales_with_mass'` | τ = O(M) with bounded constant |
| `thermal_equilibrium_principle` | Steady-state objects adopt T_Hawking |
| `cauchy_horizon_unstable` | Inner horizon is generically unstable |
| `kerr_exterior_only` | Vacuum Kerr is valid only for r ≥ r_- |

Each axiom is clearly declared and physically motivated in the source. The
thermal equilibrium principle is the most consequential — it is the bridge
between geometry (which can compute horizon temperatures) and physics (which
determines the ring temperature). Without it, you cannot assign a temperature
to the ring at all.

## The Punchline: A Comparison Table

| Property | Outer Horizon (r_+) | Ring (r=0, θ=π/2) |
|----------|--------------------|--------------------|
| Location | Δ = 0 | Σ = 0 |
| Proper time to reach | Finite | Finite (τ ~ M) |
| Temperature | T_H (from κ) | T_H (from equilibrium) |
| Entropy/Complexity | S_BH (Bekenstein) | C_ring (finite) |
| Curvature | Finite | Diverges (coordinate) |
| Physical nature | Event horizon | Geometric boundary? |

The ring looks remarkably like a horizon from a thermodynamic perspective.
The only difference is the curvature divergence — and the argument here is
that this is a feature of the coordinate description, not of the physics.

## Dependencies

- **Lean 4** (current stable toolchain)
- **Mathlib** (`Mathlib.Analysis.SpecialFunctions.Log.Basic`,
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`,
  `Mathlib.Probability.Distributions.Gaussian.Real`)
- **LogosLibrary** (upstream library providing):
  - `Relativity.SR.MinkowskiSpacetime`
  - `QuantumMechanics.Uncertainty.UnboundedOperators`

## A Note on What This Is and What It Isn't

This library does not *prove* that the ring singularity is physically benign.
That would require a full quantum gravity theory, and we don't have one. What
it does is *formalise the argument* that every physically measurable quantity
at the ring is finite, and that the ring's thermodynamic profile is
indistinguishable from that of the outer horizon. The divergence of the
Kretschner scalar may be the vacuum solution screaming that it needs matter
corrections below the inner horizon — not a signal that physics itself has
broken down.

The axioms are where the physics enters. The theorems are where the logic is
checked. Lean does not care whether you find the conclusion surprising.

## Author

**Adam Bornemann** — Logos Library Formalization Project, 2025–2026.

## License

Released under the MIT License. See the `LICENSE` file for details.