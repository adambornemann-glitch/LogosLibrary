# The GNS Pre-Hilbert Space

> *Given a continuous positive-definite function $f : \mathbb{R} \to \mathbb{C}$,
> construct a pre-inner-product space whose completion carries a strongly
> continuous unitary representation of $(\mathbb{R}, +)$ with a cyclic vector
> $\xi$ satisfying $f(t) = \langle\xi,\, U(t)\xi\rangle$.*

This is the **algebraic core** of the existence half of Bochner's theorem,
formalised in Lean 4 against Mathlib. Everything here lives before the
quotient and completion — the raw pre-inner product on formal sums, its
sesquilinear and positivity properties, the translation action, and the
norm estimates that will feed strong continuity.

## The construction

The carrier is `ℝ →₀ ℂ` — finitely supported functions $\mathbb{R} \to
\mathbb{C}$, i.e.\ formal finite $\mathbb{C}$-linear combinations of
point masses $\delta_t$. The element `Finsupp.single t c` represents
$c \cdot \delta_t$.

The **pre-inner product** induced by $f$ is

$$
\langle\alpha,\,\beta\rangle_f
\;=\;
\sum_j \sum_k \bar{c}_j\, d_k\, f(s_k - t_j)
$$

for $\alpha = \sum_j c_j\,\delta_{t_j}$ and $\beta = \sum_k d_k\,\delta_{s_k}$.
This is conjugate-linear in the first argument and linear in the second
(Mathlib/physics convention, matching `@inner ℂ`).

In Lean (`Defs.lean`):

```lean
noncomputable def pdInner (f : ℝ → ℂ) (α β : ℝ →₀ ℂ) : ℂ :=
  α.sum fun t ct =>
    β.sum fun s ds =>
      starRingEnd ℂ ct * ds * f (s - t)
```

The **translation operator** $U(t)$ sends $\delta_s \mapsto \delta_{s+t}$,
extended linearly. The **cyclic vector** is $\xi = \delta_0$. The **key
identity** tying everything together is

$$
f(t) \;=\; \langle\xi,\, U(t)\xi\rangle_f.
$$

## Why this matters

Bochner's theorem produces a finite positive Borel measure $\mu$ such that
$f(t) = \int e^{i\omega t}\,d\mu(\omega)$. The classical route goes through
the GNS construction: build a pre-Hilbert space from $f$, complete it, show
the translation action extends to a unitary group, invoke Stone's theorem to
get a spectral measure, then read off $\mu$ from the spectral data of the
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
the oscillation bound $\|f(s) - f(t)\|^2 \leq 2\,f(0)_{\mathrm{re}}\cdot
\mathrm{pdVariance}\,f\,(s-t)$ and that continuity at $0$ implies continuity
everywhere.

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

Additivity $\langle\alpha,\,\beta_1 + \beta_2\rangle = \langle\alpha,\,\beta_1\rangle
+ \langle\alpha,\,\beta_2\rangle$ and scalar multiplication $\langle\alpha,\,c \cdot
\beta\rangle = c\,\langle\alpha,\,\beta\rangle$ in the second argument. Both follow
from `Finsupp.sum_add_index` and `Finsupp.sum_smul_index` respectively, splitting
the inner sum and then distributing the outer sum via `Finset.sum_add_distrib`.

No hypotheses on $f$ are needed — linearity is purely structural.

### §4 · Conjugate symmetry (`Conjugate.lean`)

$$
\langle\beta,\,\alpha\rangle_f
\;=\;
\overline{\langle\alpha,\,\beta\rangle_f}.
$$

This is where the **Hermitian condition** $f(-t) = \overline{f(t)}$ enters:
the proof conjugates every term, swaps the two sums via `Finset.sum_comm`,
and uses $\overline{f(s-t)} = f(t-s)$ (which is exactly Hermitian symmetry
after $-(s-t) = t-s$).

Left conjugate-linearity — additivity and $\langle c\cdot\alpha,\,\beta\rangle
= \bar{c}\,\langle\alpha,\,\beta\rangle$ — is then a formal corollary of
symmetry composed with right-linearity, needing no further calculation.

### §5 · Positive semi-definiteness (`PosSemiDef.lean`)

**Bridge lemma.** Given $\alpha$ with $|\mathrm{supp}(\alpha)| = N$, enumerate
the support via `Finset.equivFin` and rewrite $\langle\alpha,\,\alpha\rangle_f$
as a $\mathrm{Fin}\,N$ double sum:

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

A separate lemma shows $\mathrm{Im}\,\langle\alpha,\,\alpha\rangle_f = 0$
(from conjugate symmetry: a complex number equal to its own conjugate is real).

### §6 · The translation action (`TransAction.lean`)

Four facts about $U(t)$:

1. **Point masses**: $U(t)(c\cdot\delta_s) = c\cdot\delta_{s+t}$.
2. **Linearity**: $U(t)(\alpha + \beta) = U(t)\alpha + U(t)\beta$ and
   $U(t)(c\cdot\alpha) = c\cdot U(t)\alpha$.
3. **Group law**: $U(s) \circ U(t) = U(s+t)$ (and $U(0) = \mathrm{id}$).
4. **Isometry**: $\langle U(t)\alpha,\, U(t)\beta\rangle_f = \langle\alpha,\,\beta\rangle_f$.

The isometry is the key structural result — it is why $U(t)$ extends to a
*unitary* operator on the completion. The proof uses `Finsupp.sum_mapDomain_index`
to reindex both sums, then observes that $(s+t) - (r+t) = s - r$.

### §7 · The cyclic vector (`Cyclic.lean`)

Define $\xi = \delta_0$ (`Finsupp.single 0 1`) and prove:

$$
f(t) \;=\; \langle\xi,\, U(t)\xi\rangle_f.
$$

The proof is three rewrites: $U(t)\xi = \delta_t$ (from §6),
$\langle\delta_0,\,\delta_t\rangle = \bar{1}\cdot 1\cdot f(t - 0)$ (from §2),
and simplification.

### §8 · Norm estimates (`NormEst.lean`)

The estimate that feeds strong continuity of $U(t)$ on the completion:

$$
\mathrm{Re}\,\langle U(t)\xi - \xi,\; U(t)\xi - \xi\rangle_f
\;=\;
2\,\bigl(f(0)_{\mathrm{re}} - \mathrm{Re}\,f(t)\bigr)
\;=\;
2\cdot\mathrm{pdVariance}\,f\,t.
$$

The first equality expands the difference using bilinearity, the isometry,
the key identity, and Hermitian symmetry. The right-hand side tends to $0$
as $t \to 0$ by continuity of $f$ at $0$.

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
$\lambda \mapsto \mathrm{Re}\,\langle\alpha + \lambda\beta,\,
\alpha + \lambda\beta\rangle \geq 0$ has non-positive discriminant.
The degenerate case ($\mathrm{Re}\,\langle\beta,\beta\rangle = 0$)
is handled separately by showing that a non-negative linear function
on $\mathbb{R}$ must have zero slope.

## Properties established (summary)

| Property | Hypothesis | File |
|:---|:---|:---|
| $\langle\alpha,\,\beta_1+\beta_2\rangle = \langle\alpha,\,\beta_1\rangle + \langle\alpha,\,\beta_2\rangle$ | — | `Linearity` |
| $\langle\alpha,\,c\cdot\beta\rangle = c\,\langle\alpha,\,\beta\rangle$ | — | `Linearity` |
| $\langle\beta,\,\alpha\rangle = \overline{\langle\alpha,\,\beta\rangle}$ | `IsHermitian f` | `Conjugate` |
| $0 \leq \mathrm{Re}\,\langle\alpha,\,\alpha\rangle$ | `PositiveDefinite f` | `PosSemiDef` |
| $U(s) \circ U(t) = U(s+t)$ | — | `TransAction` |
| $\langle U(t)\alpha,\, U(t)\beta\rangle = \langle\alpha,\,\beta\rangle$ | — | `TransAction` |
| $f(t) = \langle\xi,\, U(t)\xi\rangle$ | — | `Cyclic` |
| $\mathrm{Re}\,\langle\alpha,\beta\rangle^2 \leq \mathrm{Re}\,\langle\alpha,\alpha\rangle\cdot\mathrm{Re}\,\langle\beta,\beta\rangle$ | `PositiveDefinite f`, `IsHermitian f` | `PreHilbert` |

## What comes next

The completion machinery in `GNS/Completion.lean` will:

1. Quotient by the null space $N = \{\alpha : \langle\alpha,\alpha\rangle_f = 0\}$
   (Cauchy–Schwarz guarantees $N$ is a subspace).
2. Complete to a Hilbert space $\mathcal{H}$.
3. Extend $U(t)$ to a unitary group on $\mathcal{H}$ (isometry from §6).
4. Prove strong continuity (norm estimate from §8).
5. Apply Stone's theorem to extract the spectral measure.

## References

- G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §3.3
- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, §II.6
- C. Berg, J. P. R. Christensen, and P. Ressel, *Harmonic Analysis on Semigroups*, Ch. 3
