# Forbidden SdS: A Lean Proof That Schwarzschild-de Sitter Is Unphysical

This library formalises an argument, due to Adam Bornemann, that
**Schwarzschild-de Sitter (SdS) spacetime does not represent any physically
realisable black hole** in a universe with a positive cosmological constant.

The punchline is not that non-rotating black holes are *unlikely*. It is that
the proposition "this black hole has angular momentum J = 0" is
**operationally meaningless** — it cannot be prepared, cannot persist for any
positive time, and cannot be verified by any measurement process. The state is
not merely measure-zero; it is dynamically forbidden.

## The Argument in Plain English

The logical chain is pleasingly short:

1. Angular momentum operators satisfy canonical commutation relations:
   `[Lₓ, Lᵧ] = iℏLz` (and cyclic permutations).

2. Robertson's uncertainty principle then gives us:
   `σ_Lx · σ_Ly ≥ (ℏ/2)|⟨Lz⟩|`.

3. Any universe with Λ > 0 has a de Sitter horizon radiating at positive
   temperature. Our universe also has the CMB at 2.725 K. Either way, there
   is a thermal bath, and thermal baths excite angular momentum.

4. Once *any* component `⟨Lᵢ⟩ ≠ 0`, Robertson forces the orthogonal
   components to have nonzero uncertainty — the state has been kicked out of
   the J = 0 subspace and it is not coming back.

5. Any measurement of J takes positive time. During that time, the thermal
   bath acts. By the time your measurement completes, the state is guaranteed
   to have J ≠ 0. You cannot measure what cannot survive measurement.

Therefore: SdS is forbidden. Every black hole wobbles.

## File Structure

The proof is split across five files with a clean dependency chain:

```
AngularMomentum.lean
        │
        ▼
ThermalExcitation.lean
        │
        ▼
   Reductio.lean
        │
        ▼
   LifeTime.lean
        │
        ▼
  MeasureZero.lean
```

### `AngularMomentum.lean`

Defines the `AngularMomentumOperators` structure: three unbounded self-adjoint
operators Lₓ, Lᵧ, Lz on a Hilbert space H with a common dense domain stable
under all three, and the canonical commutation relations. Also derives the
antisymmetric commutator `[Lᵧ, Lₓ] = -iℏLz` and sets up the domain plumbing
(`ShiftedDomainConditions`) needed to invoke Robertson.

This is where you see the kind of bookkeeping that makes formalisation both
painful and valuable: you cannot just *say* "Lₓ(Lᵧψ) is well-defined" — you
must *prove* that Lᵧψ lands back in the domain of Lₓ. The common stable
domain handles this.

### `ThermalExcitation.lean`

Proves the **Robertson uncertainty principle specialised to angular momentum**:

```
σ_Lx · σ_Ly ≥ (ℏ/2) · ‖⟨ψ|Lz|ψ⟩‖
```

The proof proceeds by invoking the general Robertson inequality from the
upstream library, substituting the commutation relation `[Lₓ, Lᵧ] = iℏLz`,
and carefully tracking the norm of `iℏ` through complex conjugation. Also
provides the codimension argument: zero angular momentum imposes three real
constraints, hence is a codimension-3 submanifold of state space — measure
zero under any Gibbs measure.

### `Reductio.lean`

The *reductio ad absurdum* file. Defines the physical structures:

- `SdSParameters` and `KdSParameters` (Kerr-de Sitter)
- `ThermalBath`, `CMB` (T = 2.725 K), and `deSitterTemperature`
- `IsZeroAngularMomentumState`: a state where ⟨Lₓ⟩ = ⟨Lᵧ⟩ = ⟨Lz⟩ = 0
- `RepresentsSdS`: definitionally equal to having zero angular momentum

Then proves the three "knockout" lemmas: if *any* angular momentum expectation
value is nonzero, the state does not represent SdS. Also contains a duplicate
of the Robertson proof (the argument is load-bearing in two places).

The reductio itself: assume thermal baths do not excite angular momentum. Then
every black hole maintains ⟨Lₓ⟩ = ⟨Lᵧ⟩ = ⟨Lz⟩ = 0 despite absorbing
~10⁶⁸ CMB photons over 13.8 Gyr, each carrying angular momentum ℏ from a
random direction. The probability of perfect cancellation is exactly zero.
Contradiction.

### `LifeTime.lean`

Defines `ThermalEvolution` (norm-preserving, domain-preserving time evolution)
and introduces the key axiom:

```lean
axiom thermal_excites_after_positive_time ...
```

This axiom states: after any positive time in a thermal bath, at least one
angular momentum expectation value becomes nonzero. (See
[Axiom Transparency](#axiom-transparency) below.)

From this, the file derives:

- `SdS_forbidden_after_thermalization`: SdS is forbidden after any t > 0
- `all_BH_in_our_universe_rotating`: every black hole in our universe rotates
- `skeptic_must_deny_thermal_axiom`: if you believe SdS exists, exhibit
  your counterexample to the axiom

Then comes the *quantitative* killing blow: concrete lifetime estimates in CGS
units showing how absurdly short-lived the J = 0 state would be even if you
could prepare it. For a solar-mass black hole, the SdS lifetime is less than
**10⁻²⁴ seconds** — shorter than the strong nuclear timescale. For anything
above ~10²² grams (a small asteroid), it is less than one second.

### `MeasureZero.lean`

The **Measurement Theorem** — the philosophical crown of the proof.

Defines `MeasurementProcess` (any physical measurement taking positive time),
`OperationallyMeaningful` (a proposition is operationally meaningful if some
measurement could in principle verify it), and then proves:

- **Measurement Theorem**: For any measurement process, the outcome "J = 0" is
  impossible — the state evolves away during measurement.
- **Operational Meaninglessness**: The proposition "J = 0" is not
  operationally meaningful.
- **Bornemann's Measurement Theorem** (final form): J = 0 cannot be verified,
  cannot be prepared, and cannot persist.
- **de Sitter Measurement Theorem**: Specialised to Λ > 0 spacetimes.

Also includes the Margolus-Levitin bound as a minimum measurement time,
showing that even the *fastest possible* quantum measurement already takes long
enough for thermal excitation to act.

## Axiom Transparency

This proof introduces **one physical axiom** beyond the standard Lean/Mathlib
foundations:

```lean
axiom thermal_excites_after_positive_time
```

This asserts that a thermal bath at positive temperature generically excites
angular momentum in any quantum state after any positive time. The library
provides three independent justifications:

1. **Codimension**: J = 0 is codimension-3 in state space, hence measure zero
   under Gibbs measures.
2. **CMB Reductio**: Perfect angular momentum cancellation over 10⁶⁸ photon
   interactions across 13.8 Gyr has probability exactly zero.
3. **Robertson Bootstrap**: Once any ⟨Lᵢ⟩ ≠ 0, uncertainty in the orthogonal
   components is forced nonzero — the J = 0 state is an unstable fixed point.

If you wish to deny the conclusion, you must deny this axiom. The library
politely invites you to explain how a black hole maintains ⟨Lₓ⟩ = ⟨Lᵧ⟩ =
⟨Lz⟩ = 0 while being continuously bombarded by thermal photons carrying
angular momentum from random directions.

## Dependencies

- **Lean 4** (tested with current stable toolchain)
- **Mathlib** (`Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`,
  `Mathlib.Analysis.Real.Pi.Bounds`)
- **LogosLibrary** (upstream library providing):
  - `QuantumMechanics.Uncertainty.UnboundedOperators`
  - `QuantumMechanics.Uncertainty.Robertson`
  - `QuantumMechanics.ModularTheory.ThermalTime`

## Physical Implications

The theorem has consequences that extend well beyond black hole classification:

- **Schwarzschild-de Sitter is not a physical solution** in any Λ > 0
  universe. The physically relevant family is Kerr-de Sitter (KdS) with J ≠ 0.
- **The information paradox** is typically framed in the context of
  Schwarzschild black holes. The author formally invites proponents of the
  information paradox to reformulate it in KdS. Good luck.
- **Every black hole wobbles**, from primordial remnants to supermassive
  galactic cores. This is not a perturbative statement about small corrections
  — it is a structural prohibition.

## Author

**Adam Bornemann** (also known as Dr. Baron von Wobble-Bob)
Logos Library Formalization Project, 2025–2026.

## License

Released under the MIT License. See the `LICENSE` file for details.
