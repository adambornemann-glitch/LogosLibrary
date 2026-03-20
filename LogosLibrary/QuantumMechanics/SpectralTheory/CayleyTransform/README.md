# The Cayley Transform

> *Every self-adjoint operator on a Hilbert space is unitarily equivalent — via a single, explicit formula — to multiplication by a real variable. The Cayley transform is the first step.*

The **Cayley transform** converts an unbounded self-adjoint operator $A$ into
a bounded unitary operator $U = (A - iI)(A + iI)^{-1}$. This module develops
the transform, its inverse, and the full spectral correspondence between $A$
and $U$, within the framework of one-parameter unitary groups and their
generators.

## The transform

Given a self-adjoint generator $A$ of a one-parameter unitary group, the
Cayley transform is

$$U = I - 2i(A + iI)^{-1},$$

which is equivalent to the classical formula $U = (A - iI)(A + iI)^{-1}$.
In Lean (`Transform.lean`):

```lean
noncomputable def cayleyTransform {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa
```

The central result of the module is the **spectral correspondence**
(`Spectrum.lean`):

```lean
theorem cayley_spectrum_correspondence :
    (∃ C : ℝ, C > 0 ∧ ∀ ψ (hψ : ψ ∈ gen.domain),
      ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≥ C * ‖ψ‖) ↔
    IsUnit (cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H)
```

That is: $A - \mu$ is bounded below on $\text{dom}(A)$ if and only if
$U - w$ is invertible, where $w = (\mu - i)/(\mu + i)$ is the Möbius image.

## Why this matters

The spectral theory of bounded operators is comparatively tidy: the spectrum
lives in a compact set, the resolvent is a bounded operator-valued function,
and the functional calculus is a standard consequence. Unbounded self-adjoint
operators — which are what actually arise as observables in quantum mechanics
— have none of these comforts. The domain is a proper dense subspace, the
operator is not defined everywhere, and the spectrum is typically all of
$\mathbb{R}$.

The Cayley transform is the classical escape route. It turns an unbounded
self-adjoint operator into a bounded unitary one, translating the spectral
theory of $A$ into the spectral theory of $U$ via the Möbius map
$\mu \mapsto (\mu - i)/(\mu + i)$. This is the bridge between Stone's theorem
(which gives us the generator $A$) and the spectral theorem (which gives us
the spectral measure).

In the broader library, this module sits between the resolvent theory and the
spectral measure construction. The results here are used to transfer spectral
data between $A$ and $U$, and to characterise $\text{dom}(A)$ in terms of $U$
alone.

## Proof architecture

### §1 · The Möbius map (`Mobius.lean`)

The Möbius transformation $\mu \mapsto (\mu - i)/(\mu + i)$ sends
$\mathbb{R}$ bijectively onto the unit circle minus $\{1\}$. This file
establishes the algebraic backbone:

- **Non-degeneracy**: $\mu + i \neq 0$ for all $\mu \in \mathbb{R}$
- **Norm one**: $|(\mu - i)/(\mu + i)| = 1$, proved via
  $\overline{\mu + i} = \mu - i$
- **Key identity**: $i(1 + w) = (1 - w)\mu$ where
  $w = (\mu - i)/(\mu + i)$

The identity is the algebraic heart of the eigenvalue correspondence. It
arises from the explicit formulas

$$1 - w = \frac{2i}{\mu + i}, \qquad 1 + w = \frac{2\mu}{\mu + i},$$

which are proved by `field_simp` and `ring`.

### §2 · Unitary operators (`Unitary.lean`)

This file develops the theory of bounded unitary operators needed by the
spectral correspondence. A unitary operator satisfies $U^*U = UU^* = I$.

The main structural results are:

| Result | Statement |
|:---|:---|
| `Unitary.inner_map_map` | $\langle Ux, Uy \rangle = \langle x, y \rangle$ |
| `Unitary.norm_map` | $\lVert Ux \rVert = \lVert x \rVert$ |
| `Unitary.injective` | $U$ is injective |
| `Unitary.surjective` | $U$ is surjective (via $U^*$) |

The second half of the file proves that **normal operators bounded below are
invertible** (`normal_bounded_below_isUnit`). The argument goes: bounded
below implies closed range (Cauchy sequences of preimages converge),
normality implies dense range (via $\lVert T^* y \rVert = \lVert T y \rVert$
and the orthogonal complement argument), and closed + dense = surjective.
Combined with injectivity from the lower bound, this gives invertibility.

This yields the contrapositive used in the spectral correspondence: if
$U - w$ is *not* invertible, then for every $\varepsilon > 0$ there exists a
unit vector $\varphi$ with $\lVert(U - w)\varphi\rVert < \varepsilon$ — i.e.,
$w$ is an **approximate eigenvalue**.

### §3 · The Cayley transform (`Transform.lean`)

The core file. The Cayley transform is defined as $U = I - 2i(A + iI)^{-1}$
and the following are proved:

**Isometry** (`cayleyTransform_isometry`):
$\lVert U\varphi \rVert = \lVert \varphi \rVert$ for all $\varphi$. The
proof works by writing $U\varphi = A\psi - i\psi$ and
$\varphi = A\psi + i\psi$ where $\psi = (A + iI)^{-1}\varphi$, then
computing

$$\lVert A\psi \pm i\psi \rVert^2 = \lVert A\psi \rVert^2 + \lVert \psi \rVert^2$$

using the fact that $\text{Re}\langle A\psi, i\psi \rangle = 0$ (because
$\langle A\psi, \psi \rangle$ is real by self-adjointness).

**Unitarity** (`cayleyTransform_unitary`): $U^*U = UU^* = I$. The proof
first establishes inner product preservation via a polarisation argument,
deduces $U^*U = I$, then obtains $UU^* = I$ using surjectivity.

**Operator norm** (`cayleyTransform_norm_one`): $\lVert U \rVert = 1$.

The file also proves `self_adjoint_norm_sq_add`, the Pythagorean identity
$\lVert A\psi + i\psi \rVert^2 = \lVert A\psi \rVert^2 + \lVert \psi \rVert^2$,
which is the workhorse lemma reused across the module.

### §4 · The inverse Cayley transform (`Inverse.lean`)

Recovering $A$ from $U$. For $\varphi = (A + iI)\psi$:

$$(I - U)\varphi = 2i\psi, \qquad (I + U)\varphi = 2A\psi.$$

These give the **recovery formulas**: $\psi = (-i/2)(I - U)\varphi$ and
$A\psi = \tfrac{1}{2}(I + U)\varphi$.

The file defines `inverseCayleyOp` as a linear map on
$\text{range}(I - U)$, and proves:

- **Symmetry** (`inverseCayleyOp_symmetric`): the inverse Cayley transform
  is a symmetric operator, proved by a direct inner product computation
  using the identity
  $\langle U\chi_1, U\chi_2 \rangle = \langle \chi_1, \chi_2 \rangle$
- **Domain characterisation**
  (`generator_domain_eq_range_one_minus_cayley`):
  $\text{dom}(A) = \text{range}(I - U)$

The domain characterisation is proved as a set equality: the forward
direction uses the formula $(I - U)(A\psi + i\psi) = 2i\psi$; the reverse
direction takes $\psi$ in $\text{range}(I - U)$, writes
$\psi = c \cdot (I - U)\chi$ for some $\chi$, and traces back through the
resolvent to show $\psi \in \text{dom}(A)$.

### §5 · Eigenvalue correspondence (`Eigenvalue.lean`)

The eigenvalue-level version of the spectral correspondence:

$$\mu \in \mathbb{R} \text{ is an eigenvalue of } A \iff \frac{\mu - i}{\mu + i} \text{ is an eigenvalue of } U.$$

In Lean:

```lean
theorem cayley_eigenvalue_correspondence :
    (∃ ψ : H, ∃ hψ : ψ ∈ gen.domain, ψ ≠ 0 ∧ gen.op ⟨ψ, hψ⟩ = μ • ψ) ↔
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform gen hsa φ = ((↑μ - I) * (↑μ + I)⁻¹) • φ)
```

The forward direction: if $A\psi = \mu\psi$, set
$\varphi = (A + iI)\psi = (\mu + i)\psi$. Then
$U\varphi = (A - iI)\psi = (\mu - i)\psi = w \cdot (\mu + i)\psi = w\varphi$.

The backward direction: if $U\varphi = w\varphi$, set
$\psi = (A + iI)^{-1}\varphi$ and use $w \neq 1$ (which follows from $\mu$
being real) to solve for $A\psi = \mu\psi$.

The file also proves `cayley_shift_identity`, the **key identity**

$$(U - w)\varphi = (1 - w)(A\psi - \mu\psi)$$

where $\varphi = (A + iI)\psi$. This identity, which follows directly from
the Möbius coefficient identity of §1, is the bridge between approximate
eigenvalues of $U$ and approximate eigenvalues of $A$.

As a special case, `cayley_neg_one_eigenvalue_iff` proves that $-1$ is an
eigenvalue of $U$ if and only if $0$ is an eigenvalue of $A$.

### §6 · Spectral correspondence (`Spectrum.lean`)

The full spectral correspondence, lifting from eigenvalues to approximate
point spectra. This is the technically hardest file.

**Forward direction** (`cayley_approx_eigenvalue_forward`): if $A - \mu$ is
not bounded below (i.e., for every $C > 0$ there exists $\psi$ in the domain
with $\lVert(A - \mu)\psi\rVert < C\lVert\psi\rVert$), then $U - w$ has
approximate eigenvalues. The proof takes such a $\psi$, forms
$\varphi = (A + iI)\psi$, normalises to get a unit vector, and uses the
shift identity plus $\lVert\varphi\rVert \geq \lVert\psi\rVert$ (from the
Pythagorean identity) to transfer the smallness.

**Backward direction** (`cayley_approx_eigenvalue_backward`): if $U - w$ has
approximate eigenvalues, then $A - \mu$ is not bounded below. This is the
hard direction. Given a unit vector $\varphi$ with
$\lVert(U - w)\varphi\rVert < \varepsilon$, one must produce
$\psi \in \text{dom}(A)$ with $\lVert(A - \mu)\psi\rVert$ small relative to
$\lVert\psi\rVert$. The proof involves a delicate $\delta$-estimation
argument: setting $\psi = (A + iI)^{-1}\varphi$ and
$\delta = \lVert(A - \mu)\psi\rVert$, one shows that if $\delta$ is too
large, then $\lVert(U - w)\varphi\rVert$ is bounded below — contradicting
the approximate eigenvalue hypothesis. The lower bound comes from expanding
$\lVert(U - w)\varphi\rVert^2$ and bounding the terms using
$\text{denom} = \sqrt{1 + \mu^2}$.

**Resolvent mapping** (`cayley_maps_resolvent`): if $z \in \mathbb{C}$ has
$\text{Im}(z) \neq 0$, then $U - w$ is invertible where
$w = (z - i)/(z + i)$. The proof splits on whether $|w| < 1$ or $|w| > 1$
(it cannot equal $1$ since $\text{Im}(z) \neq 0$), and in each case factors
$U - w$ as a product of invertible operators using the Neumann series.

### §7 · Spectral measures (`SpectralMeasure.lean`)

This file defines the **Möbius image** of a Borel set,

$$\text{cayleyImage}(B) = \left\lbrace\frac{\mu - i}{\mu + i} \;\middle|\; \mu \in B\right\rbrace,$$

and the compatibility predicate `SpectralMeasuresCompatible` asserting
$E_A(B) = E_U(\text{cayleyImage}(B))$ for all Borel sets
$B \subseteq \mathbb{R}$.

The file also develops the **inverse Möbius map** $w \mapsto i(1+w)/(1-w)$
and proves it sends the unit circle minus $\{1\}$ back to $\mathbb{R}$,
establishing that `cayleyImage` and `inverseCayleyImage` are inverses.

The existence of spectral measures for self-adjoint operators follows from
the spectral theorem for bounded unitary operators (Reed & Simon, Theorem
VIII.6), which is not yet formalised in Mathlib. The results here are
**parameterised** by spectral measures satisfying the compatibility condition
— they become fully instantiated once the spectral theorem is available.

## File map

```
CayleyTransform/
├── Mobius.lean          — §1: Möbius map μ ↦ (μ-i)/(μ+i), algebraic identities
├── Unitary.lean         — §2: Unitary operators, normality, approximate eigenvalues
├── Transform.lean       — §3: Cayley transform, isometry, unitarity, operator norm
├── Inverse.lean         — §4: Inverse transform, recovery formulas, dom(A) = range(I-U)
├── Eigenvalue.lean      — §5: Eigenvalue correspondence via Möbius map
├── Spectrum.lean        — §6: Full spectral correspondence (bounded below ↔ invertible)
└── SpectralMeasure.lean — §7: Spectral measures, Möbius image, compatibility
```

## Dependencies

This module depends on the **resolvent theory** for generators of
one-parameter unitary groups, developed in the parent library
(`UnitaryEvo.Resolvent`). In particular, the existence and properties of
$(A + iI)^{-1}$ as a bounded operator are assumed from that module.

## References

- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I:
  Functional Analysis*, Academic Press, 1980, §VIII.3–VIII.4
- K. Schmüdgen, *Unbounded Self-Adjoint Operators on Hilbert Space*,
  Springer, 2012, Chapter 13
- J. von Neumann, *Allgemeine Eigenwerttheorie Hermitescher
  Funktionaloperatoren*, Math. Ann. **102** (1930), 49–131
