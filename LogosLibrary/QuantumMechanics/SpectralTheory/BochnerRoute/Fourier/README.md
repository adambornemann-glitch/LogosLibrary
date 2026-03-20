# Fourier Uniqueness for Finite Measures

> *A finite positive Borel measure on ℝ is uniquely determined by its characteristic function.*

This is the **uniqueness half** of Bochner's theorem, formalised in Lean 4
against Mathlib. It replaces the axiom `measure_eq_of_fourier_eq` that was
previously assumed in the library with a fully machine-checked proof.

## The theorem

If $\mu$ and $\nu$ are finite positive Borel measures on $\mathbb{R}$ with
the same characteristic function, i.e.

$$
\int_{\mathbb{R}} e^{i\omega t}\,d\mu(\omega)
\;=\;
\int_{\mathbb{R}} e^{i\omega t}\,d\nu(\omega)
\qquad \forall\, t \in \mathbb{R},
$$

then $\mu = \nu$.

In Lean (`Unique.lean`):

```lean
theorem fourier_uniqueness (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ↑ω * ↑t) ∂μ = ∫ ω, exp (I * ↑ω * ↑t) ∂ν) :
    μ = ν
```

## Why this matters

Bochner's theorem says that a function $f : \mathbb{R} \to \mathbb{C}$ is
continuous and positive-definite if and only if it is the characteristic
function of a finite positive Borel measure. The "only if" direction
(existence) is the hard part; the "if" direction (uniqueness) is what we
prove here. Without uniqueness, the representing measure in Bochner's
theorem is not well-defined, and the entire bridge between positive-definite
functions and spectral measures collapses.

In the broader `SpectralBridge` library, this result is the link between
the abstract functional-analytic construction (Stone's theorem, the spectral
measure) and concrete Fourier analysis.

## Proof strategy

The argument follows the classical **Lévy inversion** route. The idea is
beautifully simple in outline: convolve with an approximate identity (the
Poisson kernel), show the result depends only on the characteristic function,
then pass to the limit.

### §1 · The Poisson kernel (`Lemmas.lean`)

Define the **Poisson kernel** (normalised Lorentzian):

$$
P_\varepsilon(x)
\;=\;
\frac{1}{\pi}\,\frac{\varepsilon}{x^2 + \varepsilon^2},
\qquad \varepsilon > 0.
$$

The key computation is the **Fourier transform of the two-sided exponential**:

$$
\int_{-\infty}^{\infty} e^{-\varepsilon|t|}\,e^{i\xi t}\,dt
\;=\;
\frac{2\varepsilon}{\xi^2 + \varepsilon^2}.
$$

This is proved by splitting into half-lines $(-\infty,0]$ and $(0,\infty)$,
evaluating each via the half-line integral

$$
\int_0^\infty e^{-at}\,dt = a^{-1}, \qquad \mathrm{Re}(a) > 0,
$$

(proved by FTC for Bochner integrals), and combining via the algebraic identity
$({\varepsilon - i\xi})^{-1} + ({\varepsilon + i\xi})^{-1} = {2\varepsilon}/{(\xi^2+\varepsilon^2)}$.

The file also establishes:
- $P_\varepsilon \geq 0$, continuity, measurability
- integrability of $(1+x^2)^{-1}$ on $\mathbb{R}$ (by splitting into $[-1,1]$ and the tails)
- $\int_{\mathbb{R}} (1+x^2)^{-1}\,dx = \pi$ (by FTC + arctan limits)
- integrability of $P_\varepsilon$ on $\mathbb{R}$

### §2 · The arctan primitive (`ArctanPrim.lean`)

Integrating the Poisson kernel over an interval gives:

$$
\int_a^b P_\varepsilon(x - \omega)\,dx
\;=\;
\frac{1}{\pi}\!\left[\arctan\!\frac{b-\omega}{\varepsilon}
- \arctan\!\frac{a-\omega}{\varepsilon}\right].
$$

We call the right-hand side the **arctan recovery function**
$\varphi_\varepsilon(\omega; a, b)$, and prove:

$$
0 \;\leq\; \varphi_\varepsilon(\omega; a,b) \;\leq\; 1.
$$

The upper bound uses $\arctan(\cdot) \in (-\tfrac{\pi}{2}, \tfrac{\pi}{2})$,
so any difference of two arctangent values is strictly less than $\pi$.

### §3 · The Poisson–Fourier bridge (`Bridge.lean`)

This is the step where Fubini connects the spatial and frequency domains.
For a finite measure $\mu$ with characteristic function
$\varphi(t) = \int e^{i\omega t}\,d\mu(\omega)$:

$$
\int_{\mathbb{R}} P_\varepsilon(s - \omega)\,d\mu(\omega)
\;=\;
\frac{1}{2\pi}\int_{\mathbb{R}}
\mathrm{Re}\!\Big(e^{-ist}\,e^{-\varepsilon|t|}\,\varphi(t)\Big)\,dt.
$$

The proof uses:
1. Fubini (justified by the global bound
   $P_\varepsilon(x) \leq 1/(\pi\varepsilon)$ making the joint integrand
   dominated by an integrable constant on the product space)
2. A **conjugation trick**: $\mathrm{Re}(z) = \mathrm{Re}(\bar{z})$
   applied to swap the sign in the exponential, converting $\int e^{-i\omega t}\,d\mu$
   into $\int e^{i\omega t}\,d\mu$

**Corollary**: if $\mu$ and $\nu$ have the same characteristic function, their
Poisson integrals agree for all $s$ and all $\varepsilon > 0$.

### §4 · Arctan limits (`ArctanLim.lean`)

As $\varepsilon \to 0^+$, the arctan recovery converges pointwise to the
indicator function:

$$
\varphi_\varepsilon(\omega;\,a,b) \;\longrightarrow\;
\begin{cases}
1   & \text{if } \omega \in (a,b), \\[4pt]
\tfrac{1}{2} & \text{if } \omega = b, \\[4pt]
0   & \text{if } \omega < a \text{ or } \omega > b.
\end{cases}
$$

The proofs are direct: when $\omega \in (a,b)$, we have
$(b-\omega)/\varepsilon \to +\infty$ and $(a-\omega)/\varepsilon \to -\infty$,
so $\arctan \to \pi/2$ and $\arctan \to -\pi/2$ respectively, giving
$(1/\pi)(\pi/2 - (-\pi/2)) = 1$. The other cases are similar.

### §5 · Distribution function agreement (`Distribution.lean`)

Two results here:

**Fubini** (`integrated_poisson_eq_arctan`): swapping the order of integration,

$$
\int_{(a,b]}\!\left(\int_{\mathbb{R}} P_\varepsilon(s-\omega)\,d\mu(\omega)\right)ds
\;=\;
\int_{\mathbb{R}} \varphi_\varepsilon(\omega;\,a,b)\,d\mu(\omega).
$$

**DCT** (`arctan_integral_tendsto_measure`): since $0 \leq \varphi_\varepsilon \leq 1$
and $\varphi_\varepsilon \to \mathbf{1}_{(a,b]}$ pointwise $\mu$-a.e. (the
possible exceptions at $\omega = a$ and $\omega = b$ are null provided
$\mu\{a\} = \mu\{b\} = 0$), dominated convergence gives:

$$
\int_{\mathbb{R}} \varphi_\varepsilon(\omega;\,a,b)\,d\mu(\omega)
\;\longrightarrow\;
\mu\!\left((a,b]\right)
\qquad (\varepsilon \to 0^+).
$$

### §6 · Agreement on intervals (`Agreement.lean`)

Combining §3 and §5: if $\mu$ and $\nu$ have the same characteristic function
and $a, b$ are **continuity points** of both distribution functions (i.e.
$\mu\{a\} = \mu\{b\} = \nu\{a\} = \nu\{b\} = 0$), then

$$
\mu\!\left((a,b]\right) = \nu\!\left((a,b]\right).
$$

The argument chains: same char. function $\Rightarrow$ same Poisson integrals
$\Rightarrow$ same arctan integrals $\Rightarrow$ same limit $\Rightarrow$
same measure on $(a,b]$.

This file also proves `finite_of_measure_singleton_ge`: for each threshold
$1/(n+1)$, only finitely many points can carry that much mass (otherwise
$\mu(\mathbb{R}) = \infty$, contradicting finiteness).

### §6.5 · Continuity points are dense (`ContPoints.lean`)

The most technically involved file. The key facts:

1. **Countably many atoms** (`countable_atoms`): a finite measure on $\mathbb{R}$
   has at most countably many atoms ($\{x : \mu\{x\} \neq 0\}$ is countable).

2. **Joint non-atoms exist** (`exists_continuity_points_below`): for any $a$,
   there is a sequence $a_n \nearrow a$ with $\mu\{a_n\} = \nu\{a_n\} = 0$.
   This follows because the joint atom set is countable but every open interval
   is uncountable.

3. **Extension to all intervals** (`measure_Ioc_eq_of_fourier_eq'`): given
   arbitrary $a < b$, pick a joint non-atom $c < a$. Then $\mu(c, b] = \nu(c, b]$
   and $\mu(c, a] = \nu(c, a]$ (by approximating the right endpoint with non-atoms
   and using right-continuity of $r \mapsto \mu(c, r]$). Now:

$$
\mu(a,b]
= \mu(c,b] - \mu(c,a]
= \nu(c,b] - \nu(c,a]
= \nu(a,b].
$$

The right-continuity of $r \mapsto \mu(\text{Ioc}\;c\;r)$ is obtained via
`tendsto_measure_biInter_gt`, using the identity
$\bigcap_{r > d}\,(c, r] = (c, d]$.

### §7 · Conclusion (`Unique.lean`)

Agreement on all $(a,b]$ gives $\mu = \nu$ by `Measure.ext_of_Ioc`. Six lines.

## Supporting material: positive-definite functions

These files are not part of the uniqueness proof per se, but establish the
properties needed for the **existence** proof (Part II of Bochner's theorem).

### Definitions (`PositiveDefinite.lean`)

A function $f : \mathbb{R} \to \mathbb{C}$ is **positive-definite** if

$$
\sum_{i=1}^n \sum_{j=1}^n \bar{c}_i\,c_j\,f(t_i - t_j) \;\geq\; 0
$$

for all finite collections of points $t_1,\ldots,t_n \in \mathbb{R}$ and
coefficients $c_1,\ldots,c_n \in \mathbb{C}$.

A function is **continuous positive-definite** if it is positive-definite and
continuous at $0$ (continuity at $0$ plus positive-definiteness implies
uniform continuity everywhere).

### Properties (`PdProperties.lean`)

From positive-definiteness alone (specialising $n$, the points, and the
coefficients):

| Coefficients | Result |
|:---|:---|
| $n=1,\; c_1=1$ | $f(0) \geq 0$ (real part) |
| $n=2,\; c = (1,1)$ | $0 \leq 2\mathrm{Re} f(0) + \mathrm{Re}(f(t)+f(-t))$ |
| $n=2,\; c = (1,-1)$ | $0 \leq 2\mathrm{Re} f(0) - \mathrm{Re}(f(t)+f(-t))$ |
| $n=2,\; c = (1,i)$ | imaginary part lower bound |
| $n=2,\; c = (1,-i)$ | imaginary part upper bound |

Under **Hermitian symmetry** $f(-t) = \overline{f(t)}$ (which holds for
unitary correlation functions and Fourier transforms of positive measures,
but does *not* follow from the $\mathrm{Re} \geq 0$ condition alone):

$$
\|f(t)\| \;\leq\; \mathrm{Re}\,f(0).
$$

This is the **sharp norm bound**, proved by choosing the optimised coefficients
$c = (\overline{f(t)},\, -\|f(t)\|)$. It is the critical estimate for
dominated convergence in the existence proof.

## File map

```
BochnerRoute/
├── PositiveDefinite.lean          — Definitions: PositiveDefinite, PositiveDefiniteContinuous
├── PdProperties.lean              — PD properties, Hermitian symmetry, sharp norm bound
└── Fourier/
    └── PoissonKernel/
        └── Lemmas.lean            — §1: Poisson kernel, exponential integrals, ∫(1+x²)⁻¹=π
    ├── ArctanPrim.lean            — §2: Arctan primitive, bounds on recovery function
    ├── Bridge.lean                — §3: Poisson–Fourier bridge (Fubini + conjugation trick)
    ├── ArctanLim.lean             — §4: Pointwise limits of arctan recovery
    ├── Distribution.lean          — §5: Fubini for integrated Poisson, DCT for ε → 0
    ├── Agreement.lean             — §6: Agreement on (a,b] at continuity points
    ├── ContPoints.lean            — §6.5: Countable atoms, density, extension to all (a,b]
    └── Unique.lean                — §7: The theorem
```

## What this replaces

The axiom `measure_eq_of_fourier_eq` previously assumed in `PositiveDefinite.lean`
is now a theorem. No axioms beyond Lean's kernel and Mathlib are used.

## References

- P. Lévy, *Calcul des Probabilités* (1925), §24 (inversion formula)
- W. Rudin, *Real and Complex Analysis*, 3rd ed., §9.5
- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, §VII
