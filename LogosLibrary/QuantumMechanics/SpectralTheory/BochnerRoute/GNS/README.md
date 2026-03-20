# The GNS Construction for Bochner Existence

> *Every continuous positive-definite function f : ℝ → ℂ is the
> matrix coefficient of a strongly continuous unitary representation:
> there exist a Hilbert space 𝓗, a one-parameter unitary group U(t),
> and a cyclic vector ξ such that f(t) = ⟨ξ, U(t)ξ⟩.*

This is the **GNS theorem** (Gel'fand–Naimark–Segal, specialised to
functions on ℝ), formalised in Lean 4 against Mathlib. It is the
existence engine at the heart of Bochner's theorem: once we have U(t)
and ξ, Stone's theorem and the spectral theorem convert them into the
representing measure μ with f(t) = ∫ eⁱωᵗ dμ(ω).

## The theorem

In Lean (`Theorem.lean`):

```lean
theorem gns_theorem {f : ℝ → ℂ} (hf : IsContinuous f) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H)
      (U : ℝ → H →ₗ[ℂ] H) (ξ : H),
      (∀ t ψ φ, ⟨U t ψ, U t φ⟩ = ⟨ψ, φ⟩) ∧       -- isometry
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧       -- group law
      (∀ ψ, U 0 ψ = ψ) ∧                            -- identity
      (∀ ψ, Continuous (fun t => U t ψ)) ∧           -- strong continuity
      (∀ t, ⟨ξ, U t ξ⟩ = f t)                        -- key identity
```

The input `IsContinuous f` bundles `PositiveDefinite f`, `IsHermitian f`,
and `ContinuousAt f 0`.

## Proof architecture

The construction has two stages, mirroring the classical textbook route:

**Stage 1 — Pre-Hilbert space** (`PreHilbert/`). Build the pre-inner
product ⟨α, β⟩_f on formal sums `ℝ →₀ ℂ`, establish sesquilinearity,
positive semi-definiteness, the translation isometry, the cyclic vector
identity, Cauchy–Schwarz, and the variance estimate ‖U(t)ξ − ξ‖² =
2 · pdVariance f t.

**Stage 2 — Completion** (`Completion/`). Quotient by the null space
N = {α : ⟨α, α⟩ = 0}, complete to a Hilbert space 𝓗, extend U(t) to a
strongly continuous unitary group on 𝓗, verify the key identity at the
Hilbert space level, and package as a `OneParameterUnitaryGroup` for
Stone's theorem.

The theorem itself (`Theorem.lean`) is six lines: unwrap the
`GNSUnitaryGroup` structure and existentially pack its fields.

## File map

```
GNS/
├── PreHilbert/                 — Stage 1: pre-inner product on ℝ →₀ ℂ
│   ├── Defs.lean               ·   pdInner, translate (core definitions)
│   ├── Evolution.lean          ·   ⟨cₐδₐ, c_bδ_b⟩ = c̄ₐ c_b f(b−a)
│   ├── Linearity.lean          ·   Right-linearity, right-scalar
│   ├── Conjugate.lean          ·   Conjugate symmetry (uses IsHermitian)
│   ├── PosSemiDef.lean         ·   0 ≤ Re⟨α,α⟩ (uses PositiveDefinite)
│   ├── TransAction.lean        ·   U(t): linearity, group law, isometry
│   ├── Cyclic.lean             ·   ξ = δ₀, f(t) = ⟨ξ, U(t)ξ⟩
│   └── NormEst.lean            ·   ‖U(t)ξ − ξ‖² = 2·pdVariance f t
│
├── PreHilbert.lean             — Barrel import + Cauchy–Schwarz
│
├── Completion/                 — Stage 2: quotient, complete, unitary group
│   ├── NullSpace.lean          ·   Null space N, quotient V, InnerProductSpace.Core
│   ├── Bundler.lean            ·   GNSData structure (interface)
│   ├── Constructor.lean        ·   gnsConstruction : PD + Herm → GNSData
│   ├── UnitaryGroup.lean       ·   GNSUnitaryGroup structure (extends GNSData)
│   ├── ConstructorII/
│   │   ├── Lemmas.lean         ·   Translation lifted to quotient & completion
│   │   └── StronglyCont.lean   ·   Strong continuity (ε/3 argument)
│   ├── ConstructorII.lean      ·   gnsUnitaryConstruction : IsContinuous → GNSUnitaryGroup
│   ├── Cyclic.lean             ·   f(t) = ⟨ξ, U(t)ξ⟩_𝓗 at the Hilbert space level
│   └── ToStone.lean            ·   Package as OneParameterUnitaryGroup
│
├── Theorem.lean                — THE THEOREM: gns_theorem
└── TODO.lean                   — Uniform oscillation bound (sorry)
```

## Key design decisions

**Interface/implementation split.** `GNSData` (in `Bundler.lean`) is a
structure axiomatising what a GNS Hilbert space must provide: a space H,
an embedding ι with inner product preservation, density, and a kernel
characterisation. `Constructor.lean` provides the implementation via
quotient-then-complete. All downstream files (the unitary group, strong
continuity, the cyclic vector) depend only on `GNSData`, not on the
specific construction. If someone wants to build 𝓗 differently, they only
need to produce a `GNSData`.

**Two cyclic vector files.** `PreHilbert/Cyclic.lean` defines ξ = δ₀ and
proves f(t) = ⟨ξ, U(t)ξ⟩ at the pre-inner-product level.
`Completion/Cyclic.lean` lifts this to f(t) = ⟨ξ, U(t)ξ⟩_𝓗 at the Hilbert
space level, composing the compatibility relation U(t) ∘ ι = ι ∘ translate
with inner product preservation of ι.

**Uniform continuity instance by hand.** `Constructor.lean` proves
`gnsQuotient_uniformContinuousConstSMul` manually because Lean's instance
synthesis hits a diamond between `NormedAddCommGroup` and `Module` on the
quotient. This is infrastructure — not mathematically interesting, but
necessary for `UniformSpace.Completion.map` to work.

## TODO

`TODO.lean` contains a `sorry`'d uniform oscillation bound:

$$
\mathrm{Re}\,\langle U(t)\alpha - \alpha,\; U(t)\alpha - \alpha\rangle_f
\;\leq\;
\frac{2\,\mathrm{Re}\,\langle\alpha,\alpha\rangle_f \;\cdot\; \mathrm{pdVariance}\,f\,t}{\mathrm{Re}\,f(0)}.
$$

This bounds the pre-Hilbert norm of U(t)α − α for *any* formal sum α (not
just the cyclic vector ξ), and would give uniform strong continuity. The
proof sketch uses Cauchy–Schwarz for `pdInner` applied to the bilinearity
expansion ⟨U(t)α − α, U(t)α − α⟩ = 2⟨α, α⟩ − 2 Re⟨α, U(t)α⟩. This is
a nice-to-have corollary — the current proof of strong continuity in
`StronglyCont.lean` works without it, using the ε/3 density argument
instead.

## What this feeds into

The `OneParameterUnitaryGroup` produced by `ToStone.lean` is the input to
Stone's theorem (in `UnitaryEvo/Generator.lean`), which gives a self-adjoint
generator A. The spectral theorem then produces a projection-valued measure
E, and the representing Borel measure is μ(S) = ⟨ξ, E(S)ξ⟩. The cyclic
vector identity then yields

$$
f(t) = \langle\xi,\, U(t)\xi\rangle = \int_{\mathbb{R}} e^{i\omega t}\,d\mu(\omega),
$$

completing the existence half of Bochner's theorem.

## References

- G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §3.3
- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, §II.6
- C. Berg, J. P. R. Christensen, and P. Ressel, *Harmonic Analysis on Semigroups*, Ch. 3
- I. M. Gel'fand and M. A. Naimark, *On the imbedding of normed rings into
  the ring of operators in Hilbert space* (1943)
