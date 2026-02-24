# 1. Polar Decomposition

**What it is:**

Every closed densely-defined operator T decomposes as:
```
T = J|T|    where |T| = √(T*T)
```
- |T| is positive self-adjoint (the "modulus")
- J is a partial isometry with ker(J) = ker(T)

**Bounded case** (easier, do this first):
```
T : H →L[ℂ] H
T = U · P   where P = √(T*T), U partial isometry
```
You need:
- Positive square root of positive operator (via continuous functional calculus — you have this machinery)
- Partial isometry definition: `U*U` is projection onto `(ker U)ᗮ`
- Uniqueness: P is unique, U is unique on `(ker T)ᗮ`

**Unbounded case** (what you actually need for Tomita):
```
T : D(T) → H  closed, densely defined
T = J · |T|   where |T| = √(T*T)
```
The subtlety: T*T is only densely defined on D(T*T) = {ψ ∈ D(T) : Tψ ∈ D(T*)}

You need:
- T*T is positive self-adjoint (on its natural domain)
- Your spectral functional calculus gives √(T*T)
- Partial isometry J defined via: J(|T|ψ) = Tψ, extended by continuity

**For Tomita specifically:**

The Tomita operator S = JΔ^{1/2} where:
- S : xΩ ↦ x*Ω (antilinear, closable)
- Δ = S*S (the modular operator, positive self-adjoint)  
- J = modular conjugation (antiunitary)

So polar decomposition of S *is* the fundamental theorem.

---

## 2. Unbounded Antilinear Operators

**What it is:**

An antilinear (conjugate-linear) operator satisfies:
```
S(αψ + βφ) = ᾱ S(ψ) + β̄ S(φ)
```

**What Mathlib has:**
- Semilinear maps with ring homomorphism σ : R → S
- For antilinear: σ = starRingEnd ℂ (conjugation)
- This works fine for bounded operators

**What you need:**

Unbounded antilinear operators with:

1. **Domain theory** (you have this pattern from your linear case):
   ```lean
   structure UnboundedAntilinear (H : Type*) [InnerProductSpace ℂ H] where
     domain : Submodule ℂ H  -- or Set H with submodule proof
     op : domain → H
     antilinear : ∀ (c : ℂ) (ψ : domain), op (c • ψ) = conj c • op ψ
   ```

2. **Adjoint for antilinear operators:**
   
   For antilinear S, the adjoint S* satisfies:
   ```
   ⟨Sψ, φ⟩ = ⟨S*φ, ψ⟩   (note: NOT ⟨ψ, S*φ⟩)
   ```
   The conjugate-linearity flips which argument gets conjugated.

   Domain: D(S*) = {φ : ψ ↦ ⟨Sψ, φ⟩ extends to bounded antilinear functional}

3. **Closability:**
   
   S is closable iff: ψ_n → 0 and Sψ_n → η implies η = 0
   
   Equivalently: the graph G(S) = {(ψ, Sψ)} has closure that's still a graph

4. **Key fact for Tomita:**
   
   S*S is *linear* (antilinear ∘ antilinear = linear), so:
   - S antilinear, densely defined, closable
   - S* antilinear  
   - Δ = S*S is linear, positive, self-adjoint
   - Your existing spectral theory applies to Δ

---

## The Tomita Construction (what these enable)

Once you have both pieces:

```
M ⊆ B(H) von Neumann algebra
Ω ∈ H cyclic and separating for M

1. Define S₀ : MΩ → H by S₀(xΩ) = x*Ω
   - antilinear (since x ↦ x* is antilinear on M)
   - densely defined (Ω cyclic means MΩ dense)
   
2. S₀ is closable (uses Ω separating)
   - Let S = S̄₀ (closure)

3. Polar decomposition: S = JΔ^{1/2}
   - Δ = S*S (modular operator)
   - J = modular conjugation

4. TOMITA-TAKESAKI THEOREM:
   - JMJ = M' (commutant)
   - Δ^{it} M Δ^{-it} = M (modular automorphism group)
```

---

## Suggested Order

1. **Bounded polar decomposition** — warm up, uses your existing functional calculus
2. **Unbounded antilinear framework** — parallel your linear unbounded setup  
3. **Antilinear adjoint theory** — careful with the sesquilinear form orientation
4. **Closability for antilinear** — graph-based, same pattern as linear
5. **Unbounded polar decomposition** — combines spectral calculus + partial isometry
6. **Tomita operator construction** — now you can define S, prove closable
7. **Modular theory** — the payoff

The good news: your spectral theory infrastructure means Δ^{it} "just works" once you have Δ. The modular automorphism group σ_t(x) = Δ^{it} x Δ^{-it} is where Stone's theorem meets the functional calculus.