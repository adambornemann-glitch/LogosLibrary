/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.Superior.NanoThermo.Definition
import LogosLibrary.Superior.NanoThermo.Limits
import LogosLibrary.Superior.NanoThermo.Monotonicity
import LogosLibrary.Superior.NanoThermo.PageCurve
/-!
# Superior Nanothermodynamics

A Lean 4 formalization of nanothermodynamics as restricted modular flow,
built on the Connes–Rovelli thermal time hypothesis.

## What this library proves

Thirty years of nanothermodynamics — Hill's subdivision potential,
the Hamiltonian of mean force, anomalous heat capacities, non-extensive
entropy — were computing restricted modular flow without knowing it.

This library makes that connection formal and proves it covariant.

## Module structure

- **Definition**: Core structures (`AlgebraicCut`, `PureCut`, `NanoSystem`),
  mutual information, subdivision potential, the Hamiltonian of mean force,
  Boltzmann factor invariance, Ott covariance, and the master consistency
  theorem connecting everything to thermal time.

- **Limits**: The thermodynamic limit. Classical thermodynamics emerges as
  N → ∞: the subdivision potential vanishes, the Hamiltonian of mean force
  collapses to the bare Hamiltonian, and the modular Hamiltonian reduces
  to H_bare/T. Includes the sandwich theorem and explicit O(1/N) bounds.

- **Monotonicity**: Ordering theorems and the data processing inequality.
  More correlation → bigger cost. Hotter → bigger cost. More particles →
  smaller per-particle cost. Coarse-graining can only decrease the
  subdivision potential. The joint bound gives the complete 3D picture.

- **PageCurve**: The Page curve is a subdivision potential. Connects
  nanoclusters to evaporating black holes through the same algebraic
  structure. Proves Ott covariance of the Page curve, information
  conservation, the measurement cost of decoding Hawking radiation,
  and the universality theorem.

## Dependencies

Built on `LogosLibrary.Relativity.LorentzBoost.TTime` (the thermal time
formalization) and Mathlib.
-/
