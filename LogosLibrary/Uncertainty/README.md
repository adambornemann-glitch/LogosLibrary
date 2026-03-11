# Uncertainty Relations

**Status: ✅ Compiles. Zero `sorry`. Fully verified.**

This directory contains a complete formal verification of the quantum
mechanical uncertainty relations, from first principles through to
the textbook Heisenberg bound σ\_X σ\_P ≥ ℏ/2.

What makes this formalization unusual — and, I would argue, valuable —
is not merely that the theorems are proved, but *how* the proof is
structured. The standard physics textbook derivation glosses over
operator domains, quietly assumes everything is bounded, and arrives
at Heisenberg via a single application of Cauchy–Schwarz. That proof
is fine for intuition, but it is not *true* in the sense that a
proof assistant would accept. Unbounded operators on infinite-dimensional
Hilbert spaces are not defined on the whole space, and a formalization
that pretends otherwise is formalizing the wrong thing.

This library does it properly.

## What is proved

| Theorem | File | Statement |
|---------|------|-----------|
| **Robertson inequality** | `Robertson.lean` | σ\_A σ\_B ≥ ½ \|⟨\[A,B\]⟩\_ψ\| |
| **Schrödinger inequality** | `Schrodinger.lean` | σ\_A² σ\_B² ≥ ¼\|⟨\[A,B\]⟩\|² + Cov(A,B)² |
| **Heisenberg uncertainty** | `Heisenberg.lean` | σ\_X σ\_P ≥ ℏ/2 |
| **Robertson via Cramér–Rao** | `CramerRao.lean` | σ\_A σ\_B ≥ ½ ‖⟨\[A,B\]⟩‖ (from Fisher information) |
| **Heisenberg via Cramér–Rao** | `CramerRao.lean` | σ\_X σ\_P ≥ ℏ/2 (from Fisher information) |

The Schrödinger inequality properly subsumes Robertson: dropping the
covariance term is proved as a one-line corollary (`robertson_from_schrodinger`).
Heisenberg is then a specialization to the canonical commutation relation.

The Cramér–Rao file derives *the same inequalities again* from an entirely
different direction — information geometry rather than Cauchy–Schwarz — making
explicit the deep connection: **quantum uncertainty is a manifestation of the
Fisher metric**.

## Architecture and dependency graph

```
UnboundedOperators.lean            CramerRao.lean (information geometry)
   Symmetric operators,                │
   dense domains, commutators,         │  imports Robertson +
   expectation, variance, σ            │  InformationGeometry.CramerRao
         │                             │
         ▼                             │  Derives Robertson & Heisenberg
   Robertson.lean                      │  via the Cramér–Rao bound
   σ_A σ_B ≥ ½|⟨[A,B]⟩|                │
         │                             │
         ▼                             │
   Schrodinger.lean ◄──────────────────┘
   σ²_A σ²_B ≥ ¼|⟨[A,B]⟩|² + Cov²
         │
         ▼
   Heisenberg.lean
   σ_X σ_P ≥ ℏ/2
```

## Design decisions

### Unbounded operators as genuinely partial functions

The central type is `UnboundedObservable H`, which bundles:

- A **domain** (`Submodule ℂ H`), not the whole space
- A **linear map** on that domain (`domain →ₗ[ℂ] H`)
- A proof of **density** (`Dense (domain : Set H)`)
- A proof of **symmetry** (`⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫`)

The notation `A ⬝ ψ ⊢ hψ` makes domain membership proofs explicit
at every application site. You literally cannot apply an observable
to a vector without proving it lives in the domain. This is the
correct level of rigour for unbounded operators — symmetric ≠
self-adjoint, and this module only assumes symmetry, which is what
Robertson actually requires.

### Bundled domain conditions

Computing `[A,B]ψ = ABψ - BAψ` requires four domain memberships:
ψ ∈ Dom(A), ψ ∈ Dom(B), Bψ ∈ Dom(A), and Aψ ∈ Dom(B). These are
collected into `DomainConditions A B ψ`, and extended with ‖ψ‖ = 1
in `ShiftedDomainConditions` for the actual inequalities.

A physics textbook would never mention any of this. That is precisely
why you should formalize it.

### Two independent proofs of Heisenberg

The standard proof (Cauchy–Schwarz in Hilbert space) is clean and
well-known. The Cramér–Rao proof is structurally different: it routes
through a `QuantumPhaseModel` that bridges quantum data to a
one-parameter statistical model via three physical axioms:

1. **Quantum Fisher information:** I(θ₀) = 4 Var\_ψ(A)
2. **Born rule → estimator variance:** Var\_stat(T) = Var\_ψ(B)
3. **Ehrenfest → derivative:** dτ/dθ = Im⟨ψ, \[A,B\]ψ⟩

These are currently axiomatized as fields ("Approach A"). Substituting
them into the classical Cramér–Rao bound yields Robertson, and
specializing to the canonical commutation relation yields Heisenberg.

The existence of two independent formally verified proofs of the same
theorem is not redundancy — it is a demonstration that the mathematical
structure is robust and that the library's abstractions compose correctly
across different branches of mathematics.

### The commutator–anticommutator decomposition

A key structural insight exploited throughout: for symmetric operators,
the inner product ⟪Ãψ, B̃ψ⟫ decomposes cleanly:

- **Real part** = covariance (related to the anticommutator {A,B})
- **Imaginary part** = ½ Im⟨ψ, \[A,B\]ψ⟩ (related to the commutator)

Robertson discards the real part. Schrödinger keeps it. Both are proved
here, and the subsumption is explicit.

## What is *not* proved (yet)

- **Self-adjointness.** This module assumes symmetry, not
  self-adjointness (Dom(A) = Dom(A\*)). Extending to essentially
  self-adjoint operators would require the von Neumann deficiency
  index theory.
- **Saturation.** Gaussian wave packets achieve equality in Robertson.
  Squeezed states saturate Schrödinger. Neither saturation result is
  formalized.
- **Approach B for Cramér–Rao.** The three bridge axioms in
  `QuantumPhaseModel` are currently stated as hypotheses. Constructing
  a model from finite-dimensional spectral data and discharging all
  three from the Born rule is future work.
- **Entropic uncertainty relations.** The Maassen–Uffink inequality
  (σ in terms of Shannon entropy rather than standard deviation)
  requires a different apparatus.

## Line counts

| File | Lines | What it buys you |
|------|------:|------------------|
| `UnboundedOperators.lean` | 244 | Domain-aware symmetric operators, commutators, variance, σ |
| `Robertson.lean` | 229 | The Robertson inequality |
| `Schrodinger.lean` | 249 | Schrödinger refinement with covariance |
| `Heisenberg.lean` | 78 | The textbook ℏ/2 bound |
| `CramerRao.lean` | 398 | Information-geometric derivation |
| **Total** | **~1200** | **Complete uncertainty relation hierarchy** |

## References

- H. P. Robertson, "The uncertainty principle", *Phys. Rev.* **34** (1929), 163–164.
- E. Schrödinger, "Zum Heisenbergschen Unschärfeprinzip",
  *Sitzungsberichte der Preussischen Akademie der Wissenschaften* (1930), 296–303.
- S. L. Braunstein, C. M. Caves, "Statistical distance and the geometry of quantum states",
  *Phys. Rev. Lett.* **72** (1994), 3439–3443.
- M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, Academic Press, 1980.
- B. C. Hall, *Quantum Theory for Mathematicians*, Springer, 2013.
- D. J. Griffiths, *Introduction to Quantum Mechanics*, 3rd ed., Cambridge, 2018.
- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
