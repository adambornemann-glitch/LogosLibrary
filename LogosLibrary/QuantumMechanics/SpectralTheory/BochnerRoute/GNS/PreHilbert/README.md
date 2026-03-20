# The GNS Pre-Hilbert Space

> *Given a continuous positive-definite function f : ℝ → ℂ, construct a
> pre-inner-product space whose completion carries a strongly continuous
> unitary representation of (ℝ, +) with a cyclic vector ξ satisfying
> f(t) = ⟨ξ, U(t)ξ⟩.*

This is the **algebraic core** of the existence half of Bochner's theorem,
formalised in Lean 4 against Mathlib. Everything here lives before the
quotient and completion — the raw pre-inner product on formal sums, its
sesquilinear and positivity properties, the translation action, and the
norm estimates that will feed strong continuity.

## The construction

The carrier is `ℝ →₀ ℂ` — finitely supported functions ℝ → ℂ, i.e. formal
finite ℂ-linear combinations of point masses δₜ. The element
`Finsupp.single t c` represents c · δₜ.

The **pre-inner product** induced by f is

$$
\langle\alpha,\,\beta\rangle_f
\;=\;
\sum_j \sum_k \bar{c}_j\, d_k\, f(s_k - t_j)
$$

for α = Σⱼ cⱼ δₜⱼ and β = Σₖ dₖ δₛₖ. This is conjugate-linear in the
first argument and linear in the second (Mathlib/physics convention,
matching `@inner ℂ`).

In Lean (`Defs.lean`):

```lean
noncomputable def pdInner (f : ℝ → ℂ) (α β : ℝ →₀ ℂ) : ℂ :=
  α.sum fun t ct =>
    β.sum fun s ds =>
      starRingEnd ℂ ct * ds * f (s - t)
```

The **translation operator** U(t) sends δₛ ↦ δₛ₊ₜ, extended linearly.
The **cyclic vector** is ξ = δ₀. The **key identity** tying everything
together is

$$
f(t) \;=\; \langle\xi,\, U(t)\xi\rangle_f.
$$

## Why this matters

Bochner's theorem produces a finite positive Borel measure μ such that
f(t) = ∫ eⁱωᵗ dμ(ω). The classical route goes through the GNS
construction: build a pre-Hilbert space from f, complete it, show the
translation action extends to a unitary group, invoke Stone's theorem to
get a spectral measure, then read off μ from the spectral data of the
cyclic vector.

This directory handles the first stage — everything that can be done
*before* taking quotients or completions. The Cauchy–Schwarz inequality
(`PreHilbert.lean`) and the variance estimate (`NormEst.lean`) are the two
results that the completion machinery in `GNS/Completion.lean` will need.

## File map

Files are ordered by dependency; each builds on the previous.

```
PreHilbert/
├── Defs.lean          — §1: pdInner, translate (core definitions)
├── Evolution.lean     — §2: Evaluation on basis elements (single–single)
├── Linearity.lean     — §3: Right-linearity and right-scalar multiplication
├── Conjugate.lean     — §4: Conjugate symmetry, left conjugate-linearity
├── PosSemiDef.lean    — §5: Positive semi-definiteness, bridge to Fin N
├── TransAction.lean   — §6: Translation action: linearity, group law, isometry
├── Cyclic.lean        — §7: Cyclic vector ξ = δ₀, key identity f(t) = ⟨ξ, U(t)ξ⟩
├── NormEst.lean       — §8: ‖U(t)ξ − ξ‖² = 2·pdVariance f t
└── PreHilbert.lean    — Barrel import; Cauchy–Schwarz for pdInner
```

The adjacent `Continuity.lean` (one level up, in `BochnerRoute/`) proves
the oscillation bound ‖f(s) − f(t)‖² ≤ 2 · Re(f(0)) · pdVariance f (s − t)
and that continuity at 0 implies continuity everywhere.

## Proof strategy

### §1 · Definitions (`Defs.lean`)

Two definitions and nothing else. `pdInner f α β` computes the double
`Finsupp.sum`; `translate t α` is `Finsupp.mapDomain (· + t) α`. The module
docstring states the conventions, the mathematical context, and the
references. All downstream files import only what they need.

### §2 · Basis evaluation (`Evolution.lean`)

The workhorse lemma:

$$
\langle c_a\,\delta_a,\; c_b\,\delta_b\rangle_f
\;=\;
\bar{c}_a\, c_b\, f(b - a).
$$

Proved by unfolding `pdInner` and applying `Finsupp.sum_single_index` twice
(with the zero-at-zero side condition handled by `pdInner_aux_zero`). Marked
`@[simp]` — it is the basic rewrite rule for all later computations.

### §3 · Right-linearity (`Linearity.lean`)

Additivity ⟨α, β₁ + β₂⟩ = ⟨α, β₁⟩ + ⟨α, β₂⟩ and scalar multiplication
⟨α, c · β⟩ = c · ⟨α, β⟩ in the second argument. Both follow from
`Finsupp.sum_add_index` and `Finsupp.sum_smul_index` respectively, splitting
the inner sum and then distributing the outer sum via `Finset.sum_add_distrib`.

No hypotheses on f are needed — linearity is purely structural.

### §4 · Conjugate symmetry (`Conjugate.lean`)

$$
\langle\beta,\,\alpha\rangle_f
\;=\;
\overline{\langle\alpha,\,\beta\rangle_f}.
$$

This is where the **Hermitian condition** f(−t) = conj(f(t)) enters: the
proof conjugates every term, swaps the two sums via `Finset.sum_comm`, and
uses conj(f(s − t)) = f(t − s) (which is exactly Hermitian symmetry after
−(s − t) = t − s).

Left conjugate-linearity — additivity and ⟨c · α, β⟩ = c̄ · ⟨α, β⟩ — is
then a formal corollary of symmetry composed with right-linearity, needing
no further calculation.

### §5 · Positive semi-definiteness (`PosSemiDef.lean`)

**Bridge lemma.** Given α with |supp(α)| = N, enumerate the support via
`Finset.equivFin` and rewrite ⟨α, α⟩_f as a Fin N double sum:

$$
\langle\alpha,\,\alpha\rangle_f
\;=\;
\sum_{j=0}^{N-1}\sum_{k=0}^{N-1}
\bar{c}_j\, c_k\, f(t_k - t_j).
$$

This is *exactly* the quadratic form appearing in the `PositiveDefinite`
condition, so:

$$
0 \;\leq\; \mathrm{Re}\,\langle\alpha,\,\alpha\rangle_f.
$$

A separate lemma shows Im⟨α, α⟩_f = 0 (from conjugate symmetry: a complex
number equal to its own conjugate is real).

### §6 · The translation action (`TransAction.lean`)

Four facts about U(t):

1. **Point masses**: U(t)(c · δₛ) = c · δₛ₊ₜ.
2. **Linearity**: U(t)(α + β) = U(t)α + U(t)β and U(t)(c · α) = c · U(t)α.
3. **Group law**: U(s) ∘ U(t) = U(s + t) (and U(0) = id).
4. **Isometry**: ⟨U(t)α, U(t)β⟩_f = ⟨α, β⟩_f.

The isometry is the key structural result — it is why U(t) extends to a
*unitary* operator on the completion. The proof uses `Finsupp.sum_mapDomain_index`
to reindex both sums, then observes that (s + t) − (r + t) = s − r.

### §7 · The cyclic vector (`Cyclic.lean`)

Define ξ = δ₀ (`Finsupp.single 0 1`) and prove:

$$
f(t) \;=\; \langle\xi,\, U(t)\xi\rangle_f.
$$

The proof is three rewrites: U(t)ξ = δₜ (from §6), ⟨δ₀, δₜ⟩ = 1̄ · 1 · f(t − 0)
(from §2), and simplification.

### §8 · Norm estimates (`NormEst.lean`)

The estimate that feeds strong continuity of U(t) on the completion:

$$
\mathrm{Re}\,\langle U(t)\xi - \xi,\; U(t)\xi - \xi\rangle_f
\;=\;
2\,\bigl(\mathrm{Re}\,f(0) - \mathrm{Re}\,f(t)\bigr)
\;=\;
2\cdot\mathrm{pdVariance}\,f\,t.
$$

The first equality expands the difference using bilinearity, the isometry,
the key identity, and Hermitian symmetry. The right-hand side tends to 0
as t → 0 by continuity of f at 0.

### Cauchy–Schwarz (`PreHilbert.lean`)

The barrel file also contains the **Cauchy–Schwarz inequality** for `pdInner`:

$$
\bigl(\mathrm{Re}\,\langle\alpha,\,\beta\rangle_f\bigr)^2
\;\leq\;
\mathrm{Re}\,\langle\alpha,\,\alpha\rangle_f
\;\cdot\;
\mathrm{Re}\,\langle\beta,\,\beta\rangle_f.
$$

Proved by the standard discriminant argument: the real quadratic
λ ↦ Re⟨α + λβ, α + λβ⟩ ≥ 0 has non-positive discriminant. The degenerate
case (Re⟨β, β⟩ = 0) is handled separately by showing that a non-negative
linear function on ℝ must have zero slope.

## Properties established (summary)

| Property | Hypothesis | File |
|:---|:---|:---|
| ⟨α, β₁ + β₂⟩ = ⟨α, β₁⟩ + ⟨α, β₂⟩ | — | `Linearity` |
| ⟨α, c · β⟩ = c · ⟨α, β⟩ | — | `Linearity` |
| ⟨β, α⟩ = conj⟨α, β⟩ | `IsHermitian f` | `Conjugate` |
| 0 ≤ Re⟨α, α⟩ | `PositiveDefinite f` | `PosSemiDef` |
| U(s) ∘ U(t) = U(s + t) | — | `TransAction` |
| ⟨U(t)α, U(t)β⟩ = ⟨α, β⟩ | — | `TransAction` |
| f(t) = ⟨ξ, U(t)ξ⟩ | — | `Cyclic` |
| (Re⟨α, β⟩)² ≤ Re⟨α, α⟩ · Re⟨β, β⟩ | `PositiveDefinite f`, `IsHermitian f` | `PreHilbert` |

## What comes next

The completion machinery in `GNS/Completion.lean` will:

1. Quotient by the null space N = {α : ⟨α, α⟩_f = 0}
   (Cauchy–Schwarz guarantees N is a subspace).
2. Complete to a Hilbert space 𝓗.
3. Extend U(t) to a unitary group on 𝓗 (isometry from §6).
4. Prove strong continuity (norm estimate from §8).
5. Apply Stone's theorem to extract the spectral measure.

## References

- G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §3.3
- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, §II.6
- C. Berg, J. P. R. Christensen, and P. Ressel, *Harmonic Analysis on Semigroups*, Ch. 3