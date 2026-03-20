# The GNS Completion

> *Quotient the pre-inner-product space by its null space, complete to a
> Hilbert space, extend the translation action to a strongly continuous
> unitary group, and verify the key identity f(t) = ⟨ξ, U(t)ξ⟩ at the
> Hilbert space level.*

This directory takes the pre-inner product from `PreHilbert/` and turns it
into a genuine Hilbert space with a one-parameter unitary group — the full
output of the GNS construction. The final file packages everything into the
form required by Stone's theorem.

## The construction

Starting from the pre-inner product `pdInner f` on `ℝ →₀ ℂ`:

1. **Null space.** N = {α : ⟨α, α⟩_f = 0}. Cauchy–Schwarz shows N is the
   radical of the form (null elements are orthogonal to everything), making
   it a ℂ-submodule.

2. **Quotient.** V = (ℝ →₀ ℂ) / N inherits a genuine inner product: the
   form `pdInner f` descends to `quotientInner` on equivalence classes,
   with definiteness guaranteed by the quotienting.

3. **Completion.** 𝓗 = V̂ is the Cauchy completion, a Hilbert space over ℂ.
   The embedding ι : (ℝ →₀ ℂ) → 𝓗 (quotient then complete) is ℂ-linear,
   preserves inner products, and has dense range.

4. **Unitary group.** `translate t` preserves N (by the translation
   isometry), so it descends to an isometry U₀(t) on V, which extends
   uniquely to an isometry U(t) on 𝓗. The group law U(s+t) = U(s)∘U(t),
   the identity U(0) = id, and the inner-product isometry all lift from
   the pre-Hilbert level by density arguments.

5. **Strong continuity.** The map t ↦ U(t)ψ is continuous for every ψ ∈ 𝓗.
   Proved by an ε/3 argument: approximate ψ by a dense element from the
   image of ι, use continuity on the dense set (which reduces to continuity
   of f), and transfer via the isometry.

6. **Key identity.** With ξ = ι(δ₀) as the cyclic vector:

$$
f(t) \;=\; \langle\xi,\, U(t)\xi\rangle_{\mathcal{H}}.
$$

This composes the compatibility relation U(t) ∘ ι = ι ∘ translate(t), the
inner product preservation of ι, and `pdInner_cyclic` from `PreHilbert/`.

## Why this matters

This is the second stage of the Bochner existence proof. The first stage
(`PreHilbert/`) built the raw algebraic data; this directory promotes it to
the analytic setting where Stone's theorem applies. The final output — a
`OneParameterUnitaryGroup` — feeds directly into Stone's theorem, which
produces a spectral measure. The cyclic vector identity then identifies
f as the characteristic function of that measure, completing the existence
half of Bochner's theorem.

## File map

Files are ordered by dependency.

```
Completion/
├── NullSpace.lean              — §1: Null space N, quotient V, InnerProductSpace.Core
├── Bundler.lean                — §2: GNSData structure (bundles H, embedding, axioms)
├── Constructor.lean            — §3: gnsConstruction (builds GNSData from PD + Hermitian)
├── UnitaryGroup.lean           — §4: GNSUnitaryGroup structure (extends GNSData with U(t))
├── ConstructorII/
│   ├── Lemmas.lean             — §5a: Translation descended to quotient and completion
│   └── StronglyCont.lean       — §5b: Strong continuity (ε/3 argument)
├── ConstructorII.lean          — §5: gnsUnitaryConstruction (builds GNSUnitaryGroup)
├── Cyclic.lean                 — §6: Cyclic vector ξ, key identity f(t) = ⟨ξ, U(t)ξ⟩_H
└── ToStone.lean                — §7: Package as OneParameterUnitaryGroup for Stone
```

## Proof strategy

### §1 · Null space and quotient (`NullSpace.lean`)

The null space N = {α : pdInner f α α = 0} is shown to be a ℂ-submodule
via two key results:

- **Null orthogonality**: if α ∈ N then ⟨α, β⟩_f = 0 for all β. This is
  where Cauchy–Schwarz from `PreHilbert.lean` is consumed: Re⟨α, β⟩² ≤ 0,
  so Re⟨α, β⟩ = 0. For the imaginary part, apply the same argument to
  ⟨α, i·β⟩ and use Re(i·z) = −Im(z).

- **Translation invariance**: if α ∈ N then U(t)α ∈ N, since
  ⟨U(t)α, U(t)α⟩ = ⟨α, α⟩ = 0 by the translation isometry.

The file then constructs:
- `pdNullSubmodule`: N as a `Submodule ℂ (ℝ →₀ ℂ)`
- `GNSQuotient`: the type V = (ℝ →₀ ℂ) ⧸ N
- `quotientInner`: the descended inner product on V (well-defined by
  `pdInner_resp_left` / `pdInner_resp_right`)
- `quotientCore`: an `InnerProductSpace.Core` on V, verifying conjugate
  symmetry, positivity, definiteness, left-additivity, and left-scalar

### §2 · The GNSData bundle (`Bundler.lean`)

A structure packaging a Hilbert space H together with:
- a ℂ-linear embedding ι : (ℝ →₀ ℂ) → H
- inner product preservation: ⟨ι(α), ι(β)⟩_H = pdInner f α β
- density: range(ι) is dense in H
- kernel characterisation: ι(α) = 0 ↔ α ∈ N

This decouples the *interface* (what downstream files need) from the
*implementation* (the specific quotient-then-complete construction).

### §3 · The Hilbert space constructor (`Constructor.lean`)

`gnsConstruction` builds a `GNSData f` from `PositiveDefinite f` and
`IsHermitian f`. The construction:

1. Instantiate `InnerProductSpace.Core` on V from `quotientCore`.
2. Derive `NormedAddCommGroup V` and `InnerProductSpace ℂ V` from the core.
3. Take H = `UniformSpace.Completion V`.
4. Build ι as the composition of `Submodule.mkQ` (quotient projection) with
   `UniformSpace.Completion.toComplₗᵢ` (completion embedding).

A technical prerequisite proved here: `gnsQuotient_uniformContinuousConstSMul`,
establishing that scalar multiplication on V is uniformly continuous. Lean's
instance synthesis cannot derive this automatically due to a diamond between
`NormedAddCommGroup` and `Module`, so it is proved from the Lipschitz bound
‖c • (x − y)‖ ≤ ‖c‖ · ‖x − y‖ directly.

### §4 · The unitary group structure (`UnitaryGroup.lean`)

`GNSUnitaryGroup` extends `GNSData` with:
- `unitaryAction : ℝ → H →ₗ[ℂ] H`
- isometry, group law, identity, strong continuity
- compatibility: U(t) ∘ ι = ι ∘ translate(t)

This is a specification, not a construction — the implementation is in §5.

### §5 · The unitary group constructor (`ConstructorII.lean` + subfolder)

#### §5a · Quotient and completion lemmas (`ConstructorII/Lemmas.lean`)

Lifts every property of `translate` through two layers:

| Level | Object | Isometry | Group law | Identity |
|:---|:---|:---|:---|:---|
| Pre-Hilbert | `translate t` | `pdInner_translate` | `translate_translate` | `translate_zero` |
| Quotient V | `quotientTranslate t` | `quotientTranslate_inner` | `quotientTranslate_comp` | `quotientTranslate_zero` |
| Completion 𝓗 | `completionTranslate t` | `completionTranslate_inner` | `completionTranslate_comp` | `completionTranslate_zero'` |

The quotient lift uses `Submodule.mapQ` (since translate preserves N).
The completion lift uses `UniformSpace.Completion.map` (since
`quotientTranslate t` is uniformly continuous, being an isometry).

Linearity of `completionTranslate` is proved by density: it agrees with
the linear `quotientTranslate` on the dense image of V in 𝓗, so it
inherits additivity and scalar compatibility by continuity.

#### §5b · Strong continuity (`ConstructorII/StronglyCont.lean`)

The argument has three layers:

**On the pre-Hilbert space.** The map t ↦ ⟨translate(t) α, β⟩_f is
continuous for Finsupp α, β — each term in the double sum involves f at
a shifted argument, f is continuous, and the sum is finite.

**On the quotient.** The map t ↦ quotientTranslate(t)(mkQ α) is
continuous ℝ → V. The proof uses ‖x − y‖² = 2(‖qα‖² − cross(t)) where
cross(t) = Re⟨U₀(t)qα, U₀(t₀)qα⟩, and continuity of the cross term
gives ‖x − y‖² < ε².

**On the completion (the ε/3 argument).** For arbitrary ψ ∈ 𝓗:
1. Approximate ψ by w = ι(α) in the dense image, with dist(ψ, w) < ε/3.
2. From continuity on the dense set, find δ with
   dist(U(t)w, U(t₀)w) < ε/3 for |t − t₀| < δ.
3. Triangle inequality, using the isometry twice:

$$
\mathrm{dist}(U(t)\psi,\, U(t_0)\psi)
\;\leq\;
\underbrace{\mathrm{dist}(U(t)\psi,\, U(t)w)}_{= \mathrm{dist}(\psi, w) < \varepsilon/3}
\;+\;
\underbrace{\mathrm{dist}(U(t)w,\, U(t_0)w)}_{< \varepsilon/3}
\;+\;
\underbrace{\mathrm{dist}(U(t_0)w,\, U(t_0)\psi)}_{= \mathrm{dist}(w, \psi) < \varepsilon/3}.
$$

The barrel file `ConstructorII.lean` assembles everything into
`gnsUnitaryConstruction`, which takes `IsContinuous f` (PD + Hermitian +
continuous at 0) and produces a `GNSUnitaryGroup f`.

### §6 · The cyclic vector (`Cyclic.lean`)

Define ξ = ι(δ₀) in 𝓗 and prove the **key identity at the Hilbert space level**:

$$
f(t) \;=\; \langle\xi,\, U(t)\xi\rangle_{\mathcal{H}}.
$$

The proof is a three-step rewrite:

$$
\langle\xi,\, U(t)\xi\rangle_{\mathcal{H}}
= \langle\iota(\delta_0),\, \iota(\mathrm{translate}\;t\;\delta_0)\rangle_{\mathcal{H}}
= \mathrm{pdInner}\;f\;\delta_0\;(\mathrm{translate}\;t\;\delta_0)
= f(t).
$$

The first step uses compatibility (U(t) ∘ ι = ι ∘ translate), the second
uses inner product preservation of ι, and the third is `pdInner_cyclic`
from `PreHilbert/`.

Also proved: ⟨ξ, ξ⟩_𝓗 = f(0), so ‖ξ‖² = Re(f(0)).

### §7 · Packaging for Stone (`ToStone.lean`)

`toOneParameterUnitaryGroup` takes a `GNSUnitaryGroup` and produces a
`OneParameterUnitaryGroup` — the input type for Stone's theorem in the
`UnitaryEvo/Generator.lean` module.

The main work is promoting each `unitaryAction t : H →ₗ[ℂ] H` to a
`ContinuousLinearMap` via `LinearMap.mkContinuous` with operator norm
bound 1 (from the norm-preservation ‖U(t)ψ‖ = ‖ψ‖, itself a consequence
of the inner product isometry).

## Properties established (summary)

| Property | Where |
|:---|:---|
| N is a ℂ-submodule | `NullSpace` |
| N is translation-invariant | `NullSpace` |
| Null ⇒ orthogonal to everything | `NullSpace` |
| V = (ℝ →₀ ℂ)/N is an inner product space | `NullSpace` |
| 𝓗 = V̂ is a Hilbert space with dense ι | `Constructor` |
| U(t) : 𝓗 → 𝓗 is a ℂ-linear isometry | `ConstructorII/Lemmas` |
| U(s+t) = U(s) ∘ U(t), U(0) = id | `ConstructorII/Lemmas` |
| t ↦ U(t)ψ is continuous for all ψ | `ConstructorII/StronglyCont` |
| f(t) = ⟨ξ, U(t)ξ⟩_𝓗 | `Cyclic` |
| U(t) packages as OneParameterUnitaryGroup | `ToStone` |

## What comes next

Stone's theorem, applied to the `OneParameterUnitaryGroup` from `ToStone`,
produces a self-adjoint generator A on 𝓗. The spectral theorem then gives a
projection-valued measure E, and the representing measure μ is defined by
μ(S) = ⟨ξ, E(S)ξ⟩. The cyclic vector identity f(t) = ⟨ξ, U(t)ξ⟩ then
yields f(t) = ∫ eⁱωᵗ dμ(ω), completing the existence half of Bochner's
theorem.

## References

- G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §3.3
- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, §II.6
- C. Berg, J. P. R. Christensen, and P. Ressel, *Harmonic Analysis on Semigroups*, Ch. 3