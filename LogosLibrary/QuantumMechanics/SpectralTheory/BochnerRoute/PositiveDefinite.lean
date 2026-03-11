/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/PositiveDefinite.lean
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.Basic

import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
/-!
# Positive-Definite Functions and Bochner's Theorem

This file defines positive-definite functions on ℝ and states Bochner's theorem
as an axiom. These are foundational definitions for the spectral bridge construction.

## Main definitions

* `PositiveDefinite`: A function `f : ℝ → ℂ` satisfying the positive-definiteness condition
* `PositiveDefiniteContinuous`: Positive-definite and continuous at 0

## Main statements

* `bochner_theorem`: Every continuous positive-definite function is the Fourier transform
  of a finite measure (stated as axiom, pending full proof)

## References

* Bochner, "Monotone Funktionen, Stieltjessche Integrale und harmonische Analyse" (1933)
* [Rudin, *Functional Analysis*][rudin1991], Chapter 1

## Tags

positive-definite, Bochner theorem, Fourier transform, harmonic analysis
-/

namespace SpectralBridge.Bochner

open Complex Filter Topology MeasureTheory

/-- A function f : ℝ → ℂ is positive-definite if for all finite collections of points
    and coefficients, the quadratic form ∑ᵢⱼ c̄ᵢcⱼf(tᵢ - tⱼ) is non-negative. -/
def PositiveDefinite (f : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * f (t i - t j)).re

/-- Continuous positive-definite function: positive-definite and continuous at 0.
    Continuity at 0 plus positive-definiteness implies continuity everywhere. -/
def PositiveDefiniteContinuous (f : ℝ → ℂ) : Prop :=
  PositiveDefinite f ∧ ContinuousAt f 0

/-- Helper lemma: right-continuity from continuity on the right.
    Used in constructing Stieltjes functions from spectral measures. -/
lemma tendsto_nhdsWithin_Ici_of_tendsto_nhdsWithin_Ioi {f : ℝ → ℝ} {x : ℝ}
    (h : Tendsto f (𝓝[>] x) (𝓝 (f x))) : ContinuousWithinAt f (Set.Ici x) x := by
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ_pos, hδ⟩ := h ε hε
  refine ⟨δ, hδ_pos, fun t ht_Ici ht_dist => ?_⟩
  obtain rfl | h_lt := (Set.mem_Ici.mp ht_Ici).eq_or_lt
  · rw [dist_self]; exact hε
  · exact hδ h_lt ht_dist

/-- **Bochner's Theorem** (axiom).

Every continuous positive-definite function on ℝ is the Fourier transform of a
finite positive measure. That is, if `f` is positive-definite and continuous at 0,
then there exists a finite measure `μ` such that `f(t) = ∫ e^{iωt} dμ(ω)`.

This is stated as an axiom pending a full proof, which requires either:
- The Herglotz representation theorem approach
- Direct construction via approximation

## TODO
Prove this from first principles using mathlib's Fourier analysis. -/
axiom bochner_theorem (f : ℝ → ℂ) (hf : PositiveDefiniteContinuous f) :
  ∃ (μ : Measure ℝ),
    IsFiniteMeasure μ ∧
    ∀ t, f t = ∫ ω, exp (I * ω * t) ∂μ

/-- Uniqueness: a finite measure on ℝ is determined by its Fourier transform.

This is the injectivity of the Fourier transform on finite measures.

## TODO
Prove using Stone-Weierstrass or characteristic function theory. -/
axiom measure_eq_of_fourier_eq (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  (∀ t : ℝ, ∫ ω, exp (I * ω * t) ∂μ = ∫ ω, exp (I * ω * t) ∂ν) → μ = ν

end SpectralBridge.Bochner
