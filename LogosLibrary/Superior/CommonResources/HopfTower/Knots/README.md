# The Hopf Tower: A Lean 4 Formalization

## The Self-Similar Structure of the Division Algebra Hopf Fibrations

**Author:** Adam Bornemann
**License:** MIT
**Status:** Complete — zero `sorry`

---

## Mathematical Overview

The four normed division algebras over ℝ,

```math
\mathbb{R} \hookrightarrow \mathbb{C} \hookrightarrow \mathbb{H} \hookrightarrow \mathbb{O}
```

give rise to the four Hopf fibrations between spheres:

| Algebra | Fiber | Total Space | Base | Fibration |
|---|---|---|---|---|
| ℝ | S⁰ | S¹ | S¹ | z ↦ z² |
| ℂ | S¹ | S³ | S² | (z₁, z₂) ↦ z₁z̄₂ |
| ℍ | S³ | S⁷ | S⁴ | (q₁, q₂) ↦ q₁q̄₂ |
| 𝕆 | S⁷ | S¹⁵ | S⁸ | (o₁, o₂) ↦ o₁ō₂ |

By a theorem of Adams (1960), these are the **only** fiber bundles of spheres over spheres with sphere fibers. This library formalizes the **self-similar structure** that connects all four levels: each Hopf fibration restricts to the previous one under the canonical Cayley-Dickson embedding (zeroing out the new imaginary coordinates), and the tower terminates because the octonions are non-associative.

### What This Library Proves

The formalization establishes three interlocking structures.

**I. The Binding Theorems ("Knots")**

At each inclusion 𝕂 ↪ 𝕂', the higher Hopf map restricts to the lower Hopf map. In coordinates:

**Knot I** (ℝ ↪ ℂ): The embedding (x, y) ↦ (x, 0, y, 0) sends S¹ ↪ S³. Under this embedding,

```math
h_3(x, 0, y, 0) = x^2 - y^2, \qquad h_1(x,0,y,0) = 2xy, \qquad h_2(x,0,y,0) = 0
```

recovering the real Hopf map (x, y) ↦ (x² − y², 2xy) with one transverse component vanishing. The image of S¹ sits inside S² as the equator.

**Knot II** (ℂ ↪ ℍ): The embedding (a, b, c, d) ↦ (⟨a, b, 0, 0⟩, ⟨c, d, 0, 0⟩) sends S³ ↪ S⁷. The quaternionic Hopf map restricts to the complex Hopf map with **two** transverse components vanishing:

```math
(\alpha\bar\beta)_j = 0, \qquad (\alpha\bar\beta)_k = 0
```

**Knot III** (ℝ ↪ ℍ, composed): The composed embedding x ↦ ⟨x, 0, 0, 0⟩ sends S¹ ↪ S⁷. The quaternionic Hopf map restricted to real quaternion pairs **is** the real squaring map. Three levels in one theorem.

**Knot IV** (ℍ ↪ 𝕆): The Cayley-Dickson embedding q ↦ (q, 0) sends S⁷ ↪ S¹⁵. The octonionic Hopf map restricts to the quaternionic Hopf map with **four** transverse components vanishing (the entire right-quaternion part of the octonionic output is zero).

**Knot V** (ℝ ↪ 𝕆, composed): The full composed embedding sends S¹ ↪ S¹⁵. The octonionic Hopf map restricted to real octonion pairs is the real squaring map. Four levels in one theorem.

**II. The Fueter Restriction Chain**

The analytic counterpart of the topological tower. The Fueter operator (quaternionic Cauchy-Riemann operator) has symbol

```math
\tilde{\sigma} = \sigma_0 + \mathbf{i}\,\sigma_1 + \mathbf{j}\,\sigma_2 + \mathbf{k}\,\sigma_3
```

and the product σ̃\*σ̃ gives the Laplacian Δₙ at each level. The **same embedding** that restricts the Hopf map also restricts the Fueter operator:

```math
\Delta_8 \xrightarrow{\;\sigma_{4..7}=0\;} \Delta_4 \xrightarrow{\;\sigma_{2,3}=0\;} \Delta_2 \xrightarrow{\;\sigma_1=0\;} \Delta_1
```

At each step, the product σ̃\*σ̃ remains scalar (all imaginary parts vanish), and the real part drops from σ₀² + σ₁² + ⋯ + σ₇² down to σ₀².

**III. The Möbius Involution J**

The conjugation operator J (quaternion conjugation q ↦ q̄, octonion conjugation (a, b) ↦ (ā, −b)) satisfies four axioms at every level of the tower:

| Axiom | Statement | Role |
|---|---|---|
| Involution | J² = id | Half-twist topology |
| Anti-multiplicativity | J(ab) = J(b) · J(a) | Order reversal |
| Norm preservation | ‖J(a)‖ = ‖a‖ | Isometry |
| Unit generation | a · J(a) = ‖a‖² | Inverse construction |

The key theorem (`fiber_action_via_J`) decomposes the proof that the S³ fiber action preserves the quaternionic Hopf map into four steps, each citing exactly one axiom of J:

```math
(aq)\cdot \overline{(bq)} \;=\; (aq)\cdot(\bar{q}\,\bar{b}) \;=\; a\cdot(q\bar{q})\cdot\bar{b} \;=\; a\cdot 1\cdot\bar{b} \;=\; a\bar{b}
```

This is **why the tower ends at 𝕆**: the second step requires associativity. The full S⁷ fiber of the octonionic Hopf fibration is a Moufang loop, not a group, and the regrouping step fails for generic unit octonions. Only the embedded S³ ⊂ S⁷ (unit quaternions) forms a genuine subgroup.

### The Self-Similarity Pattern

Every binding theorem follows the same four-step structure:

1. **Embed** by zeroing out the new Cayley-Dickson coordinates
2. **Restrict**: the higher Hopf map becomes the lower Hopf map
3. **Vanish**: transverse components are zero
4. **Fiber**: the lower fiber is a sub-fiber of the higher fiber

The dimensions follow Cayley-Dickson doubling:

| Knot | Spheres | Base | Transverse | Laplacian |
|---|---|---|---|---|
| I: ℝ → ℂ | S¹ ↪ S³ | S¹ ↪ S² | 1 vanishes | Δ₁ ← Δ₂ |
| II: ℂ → ℍ | S³ ↪ S⁷ | S² ↪ S⁴ | 2 vanish | Δ₂ ← Δ₄ |
| IV: ℍ → 𝕆 | S⁷ ↪ S¹⁵ | S⁴ ↪ S⁸ | 4 vanish | Δ₄ ← Δ₈ |

Sphere dimensions: 2n+1 at each level. Base dimensions double. Transverse components: 1, 2, 4 (powers of two). This is the Cayley-Dickson construction viewed through the Hopf lens.

### The Termination

The tower cannot extend to a fifth level. A hypothetical Knot VI would require a 16-dimensional normed division algebra. By Hurwitz's theorem (1898), no such algebra exists: the only normed division algebras over ℝ are ℝ, ℂ, ℍ, 𝕆, of dimensions 1, 2, 4, 8. The next Cayley-Dickson algebra (the sedenions 𝕊) has zero divisors; the norm is no longer multiplicative.

Non-associativity is proven by explicit witness:

```math
(e_1 \cdot e_2)\cdot e_4 \neq e_1 \cdot (e_2 \cdot e_4)
```

where e₁ = (**i**, 0), e₂ = (**j**, 0), e₄ = (0, 1) are basis octonions. Meanwhile, embedded quaternions remain associative — the twist is invisible within the subalgebra and visible only when the new Cayley-Dickson coordinate is activated.

---

## File Guide

| File | Contents |
|---|---|
| `Defs.lean` | Core definitions: real/complex/quaternionic Hopf maps, Cayley-Dickson octonions 𝕆 = ℍ×ℍ, quaternion infrastructure, Fueter symbols, octonion conjugation and norm |
| `Knot_I.lean` | **Knot I**: S¹ ↪ S³, real Hopf as restriction of complex Hopf, S⁰ fiber as S¹ restriction, norm identity specialization |
| `Knot_II.lean` | **Knot II**: S³ ↪ S⁷, complex Hopf as restriction of quaternionic Hopf, fiber identity via right multiplication by S¹ |
| `Knot_III.lean` | **Knot III**: Composed S¹ ↪ S⁷, real Hopf from quaternionic, S⁰ ⊂ S¹ ⊂ S³ fiber chain, composition coherence |
| `Knot_IV.lean` | **Knot IV**: S⁷ ↪ S¹⁵, quaternionic Hopf as restriction of octonionic Hopf, 4 transverse components vanish, S³ sub-loop of S⁷ |
| `Knot_V.lean` | **Knot V**: Composed S¹ ↪ S¹⁵, real Hopf from octonionic, sphere chain S¹ ↪ S³ ↪ S⁷ ↪ S¹⁵ |
| `FueterRestriction.lean` | Fueter–Laplacian chain Δ₈ → Δ₄ → Δ₂ → Δ₁, scalar property at every level, octonionic Fueter symbol and its restriction |
| `NonAssociativity.lean` | Non-associativity of 𝕆 by witness, associativity of embedded ℍ ⊂ 𝕆, left alternativity (embedded case), norm multiplicativity for embedded pairs |
| `InclusionChain.lean` | Fiber inclusion chain S⁰ ⊂ S¹ ⊂ S³ ⊂ S⁷, S¹ as maximal torus of S³, non-commutativity of S³, S⁷ is not a group, fiber dimension formula 2ᵏ − 1 |
| `SelfSimilarity.lean` | `TowerKnotData` structure, dimension doubling pattern, transverse growth, Adams' constraint on the hypothetical next level |
| `MobiusTower.lean` | Möbius involution axioms (I–IV) at ℍ and 𝕆, restriction chain J_𝕆 → J_ℍ → J_ℝ = id, fixed points of J are ℝ, fiber-conjugation interlock, twist visibility, termination, master J theorem |
| `Synthesis.lean` | **Master theorem** `the_hopf_tower`: single conjunction of all eight structural properties across the complete tower |

---

## What Is and Is Not Proven

### Fully Proven (zero `sorry`)

- **All five binding theorems** (Knots I–V): the Hopf map at each level restricts to the previous level's Hopf map under the canonical embedding
- **Sphere preservation** at every embedding: Sⁿ ↪ S²ⁿ⁺¹
- **Transverse vanishing**: the correct number of components vanish at each level (1, 2, 4)
- **The Fueter chain** Δ₈ → Δ₄ → Δ₂ → Δ₁: restriction and scalar property at every level
- **Fiber inclusion** S⁰ ⊂ S¹ ⊂ S³ ⊂ S⁷ with group/loop structure:
  - S¹ is a subgroup (closure under multiplication, commutativity)
  - S¹ embeds as a maximal torus of S³ ≅ SU(2)
  - S³ is non-commutative (witness: **i** **j** ≠ **j** **i**)
  - Embedded S³ ⊂ S⁷ is a genuine subgroup
  - S⁷ is not a group (non-associativity of unit octonions)
- **Möbius involution J**: all four axioms (involution, anti-multiplicativity, norm preservation, unit generation) at both ℍ and 𝕆
- **Restriction coherence**: J_𝕆 ∘ embed = embed ∘ J_ℍ and J_ℍ ∘ embed = embed ∘ J_ℝ = id
- **Fixed points**: Fix(J) = ℝ at every level, with the fixed-point set closed under multiplication
- **Fiber action via J**: the four-step proof that the S³ action preserves the quaternionic Hopf map
- **Non-associativity** of 𝕆 by explicit witness
- **Associativity** of embedded ℍ ⊂ 𝕆: twist invisible inside the subalgebra
- **Dimension doubling**: 2n+1 sphere pattern, base doubling, transverse growth as powers of two
- **Norm multiplicativity** for quaternions (Euler four-square identity) and for embedded quaternion pairs in 𝕆

### Proven for Embedded Subalgebra Only

- **Left alternativity** of 𝕆: proven when one factor is an embedded quaternion, where it follows from ℍ associativity. Full alternativity (x · (x · y) = (x · x) · y for arbitrary x, y ∈ 𝕆) is not yet formalized.
- **Norm multiplicativity** of 𝕆: proven for embed(p) · embed(q) via the quaternion four-square identity. The full octonionic eight-square identity (‖xy‖ = ‖x‖‖y‖ for arbitrary x, y ∈ 𝕆) is not yet formalized.

### Not Proven (Future Work)

- **Hurwitz's theorem**: the normed division algebras over ℝ are exactly ℝ, ℂ, ℍ, 𝕆. The formalization references this as the structural reason the tower terminates, but does not prove it. The non-associativity witness serves as a weaker (but fully mechanized) substitute.
- **Adams' Hopf invariant one theorem**: the four Hopf fibrations are the *only* sphere-over-sphere fibrations. This is deep algebraic topology (Adams spectral sequence) and far beyond the scope of a coordinate-level formalization.
- **Full alternativity** of 𝕆: x(xy) = (xx)y and (xy)y = x(yy) for all x, y ∈ 𝕆. This is an 8-dimensional computation that should be achievable with `ext <;> simp <;> ring` but has not been carried out.
- **Full norm multiplicativity** of 𝕆 (the eight-square identity / Degen's theorem).
- **Moufang identities**: a(b(ac)) = ((ab)a)c etc. These characterize the precise sense in which 𝕆 is "almost associative."
- **The KMS/modular theory connection**: the `MobiusTower.lean` documentation describes a structural analogy between the Hopf tower's conjugation J and the Tomita–Takesaki modular conjugation. This analogy is *not formalized* — it is a guiding physical interpretation, not a proven theorem. Formalizing it would require: (i) a Lean 4 formalization of von Neumann algebras and modular theory, (ii) a proof that the modular J restricted to appropriate hyperfinite factors reproduces quaternionic/octonionic conjugation.
- **Topological content**: the formalization works at the level of coordinate algebra and explicit maps. It does not construct fiber bundles, prove local triviality, compute homotopy groups, or verify the long exact sequence of a fibration. It proves that certain polynomial maps between spheres have the correct restriction and vanishing properties — the *algebraic skeleton* of the Hopf tower, not its full topological flesh.

---

## Design Decisions

**Coordinate-level formalization.** All Hopf maps are defined as explicit polynomial maps between Euclidean coordinates, not as abstract fiber bundle projections. This makes every theorem a concrete algebraic identity verifiable by `ring`, `simp`, and `linarith`. The cost is that topological properties (local triviality, homotopy invariance) are not captured.

**Cayley-Dickson octonions.** The octonions are defined as 𝕆 = ℍ × ℍ with the standard Cayley-Dickson multiplication (a, b) · (c, d) = (ac − d̄b, da + bc̄). This is not yet integrated with a Mathlib `Octonion` type (which does not exist as of writing); the structure `𝕆ℝ` is self-contained.

**Quaternion algebra parameters.** The quaternions are instantiated as `QuaternionAlgebra ℝ (-1) (0) (-1)`, which gives the standard Hamilton quaternions **i**² = **k**² = −1, **j**² = −1 via Mathlib's `QuaternionAlgebra` with parameters c₁ = −1, c₂ = 0, c₃ = −1. A custom `normSq` is used rather than Mathlib's `QuaternionAlgebra.normSq` to maintain explicit control over the algebraic form.

**The "Knot" terminology.** Each binding theorem is called a "knot" because it ties two adjacent levels of the tower together. The term is not standard; in the literature these are simply "restriction" or "compatibility" results. The metaphor is that the tower is a rope, and each binding is a knot that prevents the levels from sliding apart.

---

## References

- J. F. Adams, *On the non-existence of elements of Hopf invariant one*, Ann. of Math. **72** (1960), 20–104.
- J. C. Baez, *The Octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205. [arXiv:math/0105155](https://arxiv.org/abs/math/0105155)
- J. C. Baez, J. Huerta, *Division Algebras and Supersymmetry I*, [arXiv:0909.0551](https://arxiv.org/abs/0909.0551)
- A. Hurwitz, *Über die Composition der quadratischen Formen von beliebig vielen Variabeln*, Nachr. Ges. Wiss. Göttingen (1898), 309–316.
- H. Hopf, *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*, Math. Ann. **104** (1931), 637–665.