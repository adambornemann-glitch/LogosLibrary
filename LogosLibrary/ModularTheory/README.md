# Modular Theory and Thermal Time

**Status: The cocycle identity is proved. KMS discharge is next.**

This directory is a formally verified development of Tomita–Takesaki modular
theory, the Connes cocycle (Radon-Nikodym theorem for von Neumann algebras),
the KMS condition, and the thermal time hypothesis — built in Lean 4 on
Mathlib and the Logos Library's spectral theory.

The thermal time hypothesis of Connes–Rovelli (1994),
combined with the Connes cocycle theorem, *forces* the Ott transformation
T → γT as the unique Lorentz-covariant temperature law. This is not a
convention. It is a theorem. Landsberg (T → T) contradicts the very
mathematics that makes thermal time possible.

## The physics in one page

In a generally covariant quantum theory there is no background time.
The Wheeler–DeWitt equation gives HΨ = 0. Where did time go?

Connes and Rovelli (1994) proposed: time is not a property of the
mechanics. It is a property of the *state*. Given a faithful normal state
ω on a von Neumann algebra M, Tomita–Takesaki theory produces — for
free — a one-parameter automorphism group σ_t^ω, the modular flow. The
state ω is automatically a KMS (thermal equilibrium) state at inverse
temperature β = 1 with respect to this flow. The thermal time hypothesis
identifies σ_t^ω with physical time evolution.

But σ_t^ω depends on ω. Change the state, change the flow. Is this
physical? The Connes cocycle theorem answers: yes. Different states
give flows that differ only by inner automorphisms — "gauge
transformations" in physics language. The image in the outer automorphism
group Out(M) = Aut(M)/Inn(M) is a canonical one-parameter group

    δ : ℝ → Out(M)

that depends only on the algebra M, not on any state. This is thermal time.

**The Ott correction.** The 1994 paper left the Lorentz transformation
of temperature unaddressed. This library fills the gap. The modular
parameter τ is intrinsic to M (the cocycle theorem guarantees this).
Proper time t transforms under boosts as t → t/γ. Temperature is the
ratio T = τ/t. Therefore T → γT. The Ott transformation is forced by
the invariance of τ and the covariance of t. Any other choice — in
particular Landsberg's T → T — requires τ to transform, contradicting
the cocycle theorem.

## What is here

| File | Lines | What it proves |
|------|------:|----------------|
| [**TomitaTakesaki.lean**](TomitaTakesaki.lean) | 790 | Antilinear operators, S₀(aΩ) = a\*Ω, closability, Δ, J, Δ^{it}, σ\_t, vacuum invariance |
| [**RelativeModular.lean**](RelativeModular.lean) | 378 | Two-state setup, S\_{ψ,φ}(aΩ\_φ) = a\*Ω\_ψ, relative Δ\_{ψ,φ}, spatial derivative (Dψ:Dφ)\_t |
| [**Cocycle.lean**](Cocycle.lean) | 528 | Cocycle identity, intertwining, inner equivalence, Out(M), state-independence, chain rule |
| [**KMS/PeriodicStrip.lean**](KMS/PeriodicStrip.lean) | 872 | Strips in ℂ, periodic extension, Liouville argument, bounded entire ⟹ constant |
| [**KMS/Condition.lean**](KMS/Condition.lean) | 373 | C\*-algebra dynamics, KMS condition, convexity of KMS states, KMS ⟹ invariance |
| [**KMS/Modular.lean**](KMS/Modular.lean) | 368 | Modular ⟹ KMS at β = 1, rescaling to arbitrary β, faithful normal states |
| [**ThermalTime.lean**](ThermalTime.lean) | 521 | Thermal time flow, Ott forced, Landsberg refuted, Gibbs states, Unruh/Hawking temperatures |
| **Total** | **~3,800** | |

## The logical structure

The development has three layers. Each layer feeds the next.

**Layer 1: The modular automorphism group (TomitaTakesaki.lean).**
Start with a von Neumann algebra M acting on a Hilbert space H, equipped
with a cyclic and separating vector Ω. Define the Tomita operator
S₀(aΩ) = a\*Ω on the dense subspace MΩ. Prove well-definedness (by
separability), formal adjointness with the co-Tomita operator F₀, and
closability (by the Reed–Simon criterion: a densely-defined formal adjoint
implies closability). Take the closure S, form the modular operator
Δ = S\*S, extract the modular conjugation J from the polar decomposition
S = JΔ^{1/2}. Construct the modular unitary Δ^{it} via the bounded
functional calculus (importing the spectral power function from
SpectralTheory). Prove the group law, unitarity, and adjoint = inverse.
Define σ\_t(a) = Δ^{it} a Δ^{-it} and prove it is a one-parameter group
of \*-automorphisms preserving M, with Ω as a fixed point.

**Layer 2: The cocycle and state-independence (RelativeModular + Cocycle).**
Given two faithful normal states φ, ψ on M (in standard form: same H, same
M, different cyclic/separating vectors), construct the relative Tomita
operator S\_{ψ,φ}(aΩ\_φ) = a\*Ω\_ψ and its polar decomposition yielding
Δ\_{ψ,φ}. Define the spatial derivative (Dψ : Dφ)\_t = Δ\_{ψ,φ}^{it} · Δ\_φ^{-it}.
Prove the Connes cocycle identity:

    u\_{s+t} = u\_s · σ\_s^φ(u\_t)

by inserting Δ\_φ^{-is} · Δ\_φ^{is} = 1 and recognizing the conjugation as
σ\_s^φ. Define inner equivalence of automorphisms (differing by Ad(u) for
a unitary u ∈ M), prove it is an equivalence relation, and show that σ^φ
and σ^ψ are inner-equivalent for every t. This gives the canonical flow
δ : ℝ → Out(M), independent of the choice of state.

**Layer 3: KMS and thermal time (KMS/ + ThermalTime.lean).** Define the
KMS condition: for all a, b ∈ A, there exists F holomorphic on the strip
{0 < Im z < β}, continuous and bounded on the closure, with boundary
values F(t) = ω(a · α\_t(b)) and F(t + iβ) = ω(α\_t(b) · a). Prove
convexity of KMS states. Prove KMS states are time-invariant via the
Liouville argument: the KMS function for the pair (1, a) has matching
boundary values, extends periodically to a bounded entire function, hence
is constant by Liouville. Prove rescaling: KMS at β = 1 implies KMS at
arbitrary β for the rescaled dynamics α\_t = σ\_{t/β}. Finally,
ThermalTime.lean connects the abstract flow to Lorentz covariance: the
invariance of τ and the transformation t → t/γ force T → γT (Ott), and
Landsberg is proved inconsistent with the cocycle theorem.

## Dependency graph

```
SpectralTheory/FunctionalCalc
    │
    ▼
TomitaTakesaki.lean          KMS/PeriodicStrip.lean
  S₀, Δ, J, Δ^{it}, σ_t       Strips, Liouville
    │                              │
    ├──────────────┐               ▼
    ▼              │          KMS/Condition.lean
RelativeModular    │            KMS condition, convexity,
  S_{ψ,φ},         │            invariance proof
  Δ_{ψ,φ},         │               │
  (Dψ:Dφ)_t        │               ▼
    │              │          KMS/Modular.lean
    ▼              │            Modular ⟹ KMS at β=1,
Cocycle.lean       │            rescaling to β
  cocycle identity,│               │
  Out(M),          │               │
  state-independence               │
    │              │               │
    └──────────────┴───────────────┘
                   │
                   ▼
            ThermalTime.lean
              δ : ℝ → Out(M) IS time
              T = τ/t, Ott forced
              Landsberg refuted
              Gibbs, Unruh, Hawking
```

## Key theorems for physicists

**The cocycle identity** (Cocycle.lean, `connes_cocycle_identity`). For
states φ, ψ on M with spatial derivative u\_t = (Dψ : Dφ)\_t:

    u\_{s+t} = u\_s · σ\_s^φ(u\_t)

This is the noncommutative Radon-Nikodym theorem: modular flows of different
states differ by inner automorphisms, just as Radon-Nikodym derivatives of
different measures differ by a multiplicative factor.

**State-independence** (Cocycle.lean, `modular_flow_state_independent`).
For all t, σ\_t^φ and σ\_t^ψ define the same class in Out(M). The thermal
time flow δ : ℝ → Out(M) is intrinsic to M.

**KMS invariance** (Condition.lean, `IsKMSState.isInvariant`). Every KMS
state is time-invariant: ω ∘ α\_t = ω. Proof: Liouville's theorem applied
to the periodic extension of the KMS function for (1, a).

**Ott is forced** (ThermalTime.lean, `thermal_time_forces_ott`). The
thermal time relation t = τ/T, with τ invariant and t → t/γ, implies
T → γT. One line of algebra: τ/(t/γ) = γ(τ/t) = γT.

**Ott is unique** (ThermalTime.lean, `ott_unique_from_thermal_time`). Any
transformation T → f(v)·T preserving t = τ/T under boosts satisfies
f(v) = γ(v). Specialize to T = τ = 1.

**Landsberg contradicts the cocycle theorem** (ThermalTime.lean,
`landsberg_inconsistent_with_thermal_time`). Under T → T with t → t/γ,
maintaining t = τ/T forces τ → τ/γ. But the cocycle theorem says τ is
intrinsic to M and cannot transform. Contradiction.

## Axiom inventory

The development uses three categories of hypotheses:

**Bundled structure hypotheses** (not axioms — dischargeable by construction):

| Hypothesis | Where | Status |
|------------|-------|--------|
| `TomitaTheorem` (JMJ = M', Δ^{it}MΔ^{-it} = M) | TomitaTakesaki | Hard; requires full Tomita proof |
| `ModularOperatorData` (Δ, spectral measure) | TomitaTakesaki | From von Neumann's theorem + spectral theorem |
| `ModularConjugationData` (J, involutive, antiunitary) | TomitaTakesaki | From polar decomposition |
| `IntertwiningData` (σ^ψ = Ad(u) ∘ σ^φ) | Cocycle | Medium; relative Tomita theorem |
| `ChainRuleData` (chain rule for cocycles) | Cocycle | Medium; factorization of relative Δ |
| `RadonNikodymSurjectivity` (every cocycle is spatial) | Cocycle | Hard; Connes inverse construction |
| `SpatialDerivativeUnitarity` | RelativeModular | Standard; product of unitaries |

**True axioms** (currently irreducible):

| Axiom | Where | Why |
|-------|-------|-----|
| `relative_formal_adjoint_cross` | RelativeModular | Cross-inner product in standard form |
| `gibbs_modular_flow` | ThermalTime | Δ^{iτ} = e^{iHτ} for Gibbs states |
| `ClosabilityFromDenseAdjoint` | TomitaTakesaki | Reed–Simon Thm. VIII.1 |

**External hypotheses** (passed as function arguments):

| Hypothesis | Where | Why |
|------------|-------|-----|
| Morera extension (periodic + continuous ⟹ entire) | PeriodicStrip, Condition | Not yet in Mathlib |

The path to discharging most bundled hypotheses runs through the spectral
calculus already built in SpectralTheory/. The hardest is
`RadonNikodymSurjectivity`, which requires constructing a state from a
cocycle via analytic continuation to imaginary time — the full power of the
KMS strip machinery.

## The 1994 paper: what we correct

Connes and Rovelli, "Von Neumann algebra automorphisms and
time-thermodynamics relation in generally covariant quantum theories,"
Class. Quant. Grav. 11 (1994), 2899–2917. [gr-qc/9406019]

The paper is correct in everything it states. It is incomplete in what it
does not state. Specifically:

Equation (44) writes α\_t = γ\_{βt} with β as an unadorned constant —
implicitly adopting the Landsberg convention that inverse temperature is
frame-independent. The authors acknowledged "a certain amount of vagueness
in the formulation" (p. 22). This vagueness conceals a tension: the
cocycle theorem guarantees that the modular parameter τ is intrinsic to
the algebra and cannot transform under Lorentz boosts, while proper time
t must transform as t → t/γ. The relation t = τ/T = βτ then forces β to
transform as β → β/γ, equivalently T → γT (Ott). The Landsberg convention
β → β requires τ → τ/γ, contradicting the cocycle theorem.

This library fills the gap. The completion is unique: Ott is the only
temperature transformation compatible with both special relativity and
the modular structure of quantum statistical mechanics.

## What is not here (yet)

| Planned | Depends on | Status |
|---------|-----------|--------|
| Full Tomita proof (discharge `TomitaTheorem`) | Unbounded polar decomposition | Planned |
| KMS discharge (concrete σ\_t satisfies `IsKMSState`) | Spectral calculus for Δ^{iz} | Next target |
| Connes inverse (discharge `RadonNikodymSurjectivity`) | KMS strip + analytic continuation | Planned |
| Type III classification | Cocycle + flow of weights | Future |
| Haag–Hugenholtz–Winnink | KMS + GNS | Future |
| Bisognano–Wichmann | Modular theory + Wightman axioms | Future |

The most impactful next step is the **KMS discharge**: proving that the
vacuum state ω(a) = ⟨Ω, aΩ⟩, equipped with the modular automorphism group
σ\_t from TomitaTakesaki.lean, satisfies `IsKMSState ω σ 1` as a theorem
rather than as a hypothesis in `ModularTheoryData`. This requires
constructing the KMS function F\_{a,b}(z) = ⟨Ω, a Δ^{iz} b Ω⟩ using the
spectral calculus for complex powers of Δ, verifying analyticity on the
strip, and checking the boundary conditions. The spectral machinery in
SpectralTheory/FunctionalCalc already provides the foundation.

## Building

Depends on SpectralTheory (for the functional calculus), Relativity (for the
Lorentz factor), and Mathlib.

## References

### Modular theory
- M. Tomita, "Quasi-standard von Neumann algebras" (1967, unpublished)
- M. Takesaki, "Tomita's theory of modular Hilbert algebras and its
  application," Lecture Notes in Mathematics 128, Springer, 1970
- M. Takesaki, *Theory of Operator Algebras I–III*, Springer, 1979–2003

### The cocycle and classification
- A. Connes, "Une classification des facteurs de type III,"
  Ann. Sci. École Norm. Sup. 6 (1973), 133–252
- A. Connes, *Noncommutative Geometry*, Academic Press, 1994

### Thermal time
- A. Connes, C. Rovelli, "Von Neumann algebra automorphisms and
  time-thermodynamics relation in generally covariant quantum theories,"
  Class. Quant. Grav. 11 (1994), 2899–2917 [gr-qc/9406019]
- C. Rovelli, M. Smerlak, "Thermal time and Tolman–Ehrenfest effect,"
  Class. Quant. Grav. 28 (2011), 075007

### KMS condition
- R. Kubo, "Statistical-mechanical theory of irreversible processes,"
  J. Phys. Soc. Japan 12 (1957), 570–586
- P.C. Martin, J. Schwinger, "Theory of many-particle systems. I,"
  Phys. Rev. 115 (1959), 1342–1373
- R. Haag, N. Hugenholtz, M. Winnink, "On the equilibrium states in
  quantum statistical mechanics," Comm. Math. Phys. 5 (1967), 215–236

### Temperature transformation
- H. Ott, "Lorentz-Transformation der Wärme und der Temperatur,"
  Z. Physik 175 (1963), 70–104
- T.-T. Paetz, "An analysis of the 'thermal-time concept' of Connes and
  Rovelli," Diploma thesis, Georg-August-Universität Göttingen, 2010

### Critical assessments
- N. Swanson, "Can quantum thermodynamics save time?,"
  Philosophy of Science 88 (2021), 281–302
- E.Y.S. Chua, "The time in thermal time," J. Gen. Phil. Sci. (2025)