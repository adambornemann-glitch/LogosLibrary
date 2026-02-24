# Uncertainty Relations

This directory formalizes the quantum mechanical uncertainty relations.

## File structure

* `UnboundedOperators.lean` — Foundation: symmetric operators, domains, commutators
* `Robertson.lean` — The Robertson inequality: σ_A σ_B ≥ ½|⟨[A,B]⟩|
* `Schrödinger.lean` — The Schrödinger refinement with covariance
* `Heisenberg.lean` — The textbook ℏ/2 bound for position-momentum

## Dependency graph
```
UnboundedOperators
       ↓
   Robertson
       ↓
  Schrödinger
       ↓
  Heisenberg
```
