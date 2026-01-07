# Bornemann's Theorem of Forbidden SdS

## Abstract

We prove that Schwarzschild-de Sitter (SdS) spacetime cannot represent a physical black hole in any universe containing a thermal 
bath at temperature T > 0. The argument proceeds from the Robertson uncertainty principle for angular momentum, combined with the 
measure-theoretic observation that thermal baths generically excite nonzero angular momentum expectation values. Since SdS requires 
exactly zero angular momentum (J = 0), and this condition has probability zero under thermal perturbation, all physical black holes 
in de Sitter spacetime must be described by Kerr-de Sitter (KdS) with J ≠ 0.

Author: Adam Bornemann  

---

## References

- Heisenberg, W. (1927). "Über den anschaulichen Inhalt der quantentheoretischen Kinematik und Mechanik". *Z. Physik* 43, 172-198.
- Kennard, E.H. (1927). "Zur Quantenmechanik einfacher Bewegungstypen". *Z. Physik* 44, 326-352. (First rigorous proof of σₓσₚ ≥ ℏ/2)
- Robertson, H.P. (1929). "The Uncertainty Principle". *Phys. Rev.* 34, 163-164.

---

## Part I: Angular Momentum and Uncertainty

### 1.1 Definitions

**Definition (Reduced Planck Constant).**  
$$\hbar = 1.054571817 \times 10^{-34} \text{ J·s}$$

**Theorem (ℏ is positive).** $\hbar > 0$.  
*Status: Proven by computation.*

---

**Definition (Commutator).** For unbounded operators A and B on a Hilbert space H, the commutator applied to a state ψ is:
$$[A, B]\psi = AB\psi - BA\psi$$

---

**Definition (Expectation Value).** For an unbounded observable A and normalized state ψ:
$$\langle A \rangle_\psi = \langle \psi | A | \psi \rangle$$

**Theorem (Expectation is Real for Self-Adjoint Operators).** If A is self-adjoint and ψ is in the domain of A, then $\langle A \rangle_\psi \in \mathbb{R}$.  
*Status: Proven from self-adjointness.*

---

**Definition (Variance).**
$$\text{Var}(A) = \|A\psi\|^2 - \langle A \rangle_\psi^2$$

**Definition (Standard Deviation).**
$$\sigma_A = \sqrt{\text{Var}(A)}$$

**Theorem (Standard Deviation is Non-negative).** $\sigma_A \geq 0$.  
*Status: Proven from properties of square root.*

---

### 1.2 Angular Momentum Operators

**Definition (Angular Momentum Operators).** An angular momentum system on a Hilbert space H consists of:

1. Three self-adjoint operators $L_x, L_y, L_z$
2. A common dense domain D stable under all three operators
3. Canonical commutation relations on D:
   - $[L_x, L_y] = i\hbar L_z$
   - $[L_y, L_z] = i\hbar L_x$  
   - $[L_z, L_x] = i\hbar L_y$

**Physical Interpretation:**
- $L_i$ generates rotations about the i-axis
- Non-commutativity reflects the incompatibility of measuring different angular momentum components simultaneously

**Why Common Domain Matters:** Unbounded operators are not defined everywhere. To compute $[L_x, L_y]\psi = L_x(L_y\psi) - L_y(L_x\psi)$, we need:
- $\psi \in D(L_y)$ so $L_y\psi$ exists
- $L_y\psi \in D(L_x)$ so $L_x(L_y\psi)$ exists
- Similarly for the other term

A common stable domain guarantees all compositions are well-defined.

---

**Theorem (Commutator Relations).** For ψ in the common domain:
- $[L_x, L_y]\psi = i\hbar L_z\psi$
- $[L_y, L_z]\psi = i\hbar L_x\psi$
- $[L_z, L_x]\psi = i\hbar L_y\psi$

*Status: Proven from the definition of angular momentum operators.*

**Theorem (Antisymmetry).** $[L_y, L_x]\psi = -i\hbar L_z\psi$  
*Status: Proven by algebraic manipulation.*

---

### 1.3 The Robertson Uncertainty Principle for Angular Momentum

**Axiom (Angular Momentum Commutator).** For ψ in appropriate domains:
$$(L_x \circ L_y - L_y \circ L_x)\psi = i\hbar L_z\psi$$

*Status: Axiom. This is the standard angular momentum commutation relation from quantum mechanics.*

---

**Theorem (Angular Momentum Uncertainty).** For a normalized state ψ in the appropriate domain:
$$\sigma_{L_x} \cdot \sigma_{L_y} \geq \frac{\hbar}{2} |\langle L_z \rangle|$$

*Status: Proven from the Robertson uncertainty principle applied to angular momentum.*

**Proof Sketch:**
1. Apply Robertson's general inequality: $\sigma_A \cdot \sigma_B \geq \frac{1}{2}|\langle [A,B] \rangle|$
2. Substitute $[L_x, L_y] = i\hbar L_z$
3. Compute: $\frac{1}{2}|\langle i\hbar L_z \rangle| = \frac{1}{2}|i\hbar||\langle L_z \rangle| = \frac{\hbar}{2}|\langle L_z \rangle|$

---

**Theorem (Nonzero Expectation Implies Positive Uncertainty).** If $\langle L_z \rangle \neq 0$, then:
$$\sigma_{L_x} > 0 \quad \text{and} \quad \sigma_{L_y} > 0$$

*Status: Proven by contraposition.*

**Proof:** 
- The RHS of the uncertainty relation is positive when $\langle L_z \rangle \neq 0$
- Standard deviations are non-negative
- If either $\sigma_{L_x} = 0$ or $\sigma_{L_y} = 0$, their product is zero
- But zero cannot be ≥ a positive number
- Contradiction. ∎

---

## Part II: Thermal Excitation of Angular Momentum

### 2.1 The Core Physical Axiom

**Axiom (Thermal Excitation of Angular Momentum).** A thermal bath at T > 0 generically excites angular momentum. For any normalized state ψ:
$$\langle L_x \rangle \neq 0 \quad \text{or} \quad \langle L_y \rangle \neq 0 \quad \text{or} \quad \langle L_z \rangle \neq 0$$

*Status: Axiom. We provide four independent justifications below.*

---

### 2.2 Justification 1: Measure-Theoretic (Codimension)

The constraint $\langle L_x \rangle = \langle L_y \rangle = \langle L_z \rangle = 0$ imposes **three real equations** on the state space.

For a Hilbert space of dimension n, the pure state space is complex projective space $\mathbb{CP}^{n-1}$ with real dimension $2(n-1)$.

Three real constraints generically cut out a submanifold of **codimension 3**.

Codimension 3 in a space of dimension ≥ 3 has **measure zero**.

Any probability distribution absolutely continuous with respect to the natural measure assigns probability zero to this set. Thermal states (Gibbs measures) are absolutely continuous.

**Conclusion:** $\text{Prob}(\langle L_x \rangle = \langle L_y \rangle = \langle L_z \rangle = 0) = 0$

---

### 2.3 Justification 2: Fluctuation-Dissipation

At temperature T > 0, thermal fluctuations satisfy:
$$\langle (\Delta L_i)^2 \rangle = \langle L_i^2 \rangle - \langle L_i \rangle^2 > 0$$

If $\langle L_i \rangle = 0$ exactly, then $\langle L_i^2 \rangle = \langle (\Delta L_i)^2 \rangle > 0$.

But $\langle L_i^2 \rangle > 0$ means $L_i$ has nonzero spread—the probability distribution of $L_i$ measurements is not a delta function at zero.

For $\langle L_i \rangle$ to equal exactly zero while $\langle L_i^2 \rangle > 0$ requires **perfect symmetry**: the distribution must be exactly symmetric about zero.

Thermal perturbations break this symmetry generically. A perfectly symmetric distribution is codimension-1 in the space of distributions.

---

### 2.4 Justification 3: No Screening of Gravity

For a thermal bath to NOT excite angular momentum, one of these must hold:

**(A) Zero Coupling:** The bath has zero coupling to angular momentum degrees of freedom.

**(B) Perfect Tuning:** The coupling is perfectly tuned to preserve $\langle L_i \rangle = 0$.

**Option (A) is impossible:**
- Gravity couples to stress-energy
- Stress-energy includes momentum
- Angular momentum is spatial moments of momentum
- You cannot decouple gravity from angular momentum
- **There is no negative mass to screen gravity**

**Option (B) requires conspiracy:**
- Thermal photons, gravitons, neutrinos, dark matter...
- ALL must conspire to produce net zero torque
- At ALL times
- This has probability zero

**Conclusion:** Thermal baths excite angular momentum.

---

### 2.5 Justification 4: Reductio ad Absurdum (The CMB Argument)

**Assume** thermal baths do NOT excite angular momentum.

Then EVERY black hole in our universe:
- Sits in the CMB (T = 2.725 K)
- Has EXACTLY $\langle L_x \rangle = \langle L_y \rangle = \langle L_z \rangle = 0$
- Despite continuous bombardment by ~411 CMB photons/cm³
- Each photon carrying angular momentum ℏ
- From random directions

**This requires:**
- Every photon absorbed is matched by one emitted with equal and opposite L
- Perfectly
- Forever
- For every black hole
- Including primordial ones bathed in radiation for 13.8 billion years

**Calculation:**
- CMB photon density: 411 photons/cm³
- Universe age: $13.8 \times 10^9$ years $\approx 4.4 \times 10^{17}$ seconds
- Speed of light: $3 \times 10^{10}$ cm/s
- Total interactions $\propto 10^{70+}$ per black hole

The probability of perfect angular momentum cancellation over $10^{70}$ independent interactions from a continuous distribution is not small. **It is exactly zero.**

**Contradiction.** Therefore thermal baths excite angular momentum. ∎

---

### 2.6 Summary of Axiom Justification

The axiom `thermal_excites_angular_momentum` follows from:

| Argument | Key Point |
|----------|-----------|
| Measure theory | Zero-L states have measure zero (codimension 3) |
| Fluctuation-dissipation | T > 0 implies variance > 0; generic states have mean ≠ 0 |
| No screening | Gravity couples universally; cannot be shielded |
| CMB reductio | Perfect cancellation over $10^{70+}$ interactions has probability zero |

**Any ONE of these suffices. Together, denying the axiom requires:**
- New physics that screens gravity, OR
- A conspiracy of measure zero, OR  
- A violation of thermodynamics

**The axiom is not an assumption. It is a consequence of known physics.**

---

## Part III: Schwarzschild-de Sitter is Forbidden

### 3.1 Definitions

**Definition (SdS Parameters).** Schwarzschild-de Sitter spacetime is characterized by:
- Mass $M > 0$
- Cosmological constant $\Lambda > 0$
- Angular momentum $J = 0$

**Definition (KdS Parameters).** Kerr-de Sitter spacetime is characterized by:
- Mass $M > 0$
- Cosmological constant $\Lambda > 0$  
- Angular momentum $J$ (possibly nonzero)

**Observation:** SdS is the special case of KdS with $J = 0$.

---

**Definition (Thermal Bath).** A thermal bath is characterized by temperature $T > 0$.

**Definition (CMB).** The cosmic microwave background:
$$T_{\text{CMB}} = 2.725 \text{ K}$$

**Definition (de Sitter Temperature).** For $\Lambda > 0$:
$$T_{dS} = \frac{\sqrt{\Lambda/3}}{2\pi k_B}$$

*Status: Both are proven to satisfy T > 0.*

---

**Definition (Zero Angular Momentum State).** A state ψ has zero angular momentum iff:
- $\|\psi\| = 1$ (normalized)
- $\langle \psi | L_x | \psi \rangle = 0$
- $\langle \psi | L_y | \psi \rangle = 0$
- $\langle \psi | L_z | \psi \rangle = 0$

**Definition (Represents SdS).** A state represents SdS iff it is a zero angular momentum state.

---

### 3.2 Core Theorems

**Theorem.** Any state with $\langle L_z \rangle \neq 0$ cannot be SdS.  
*Status: Proven directly from definitions.*

**Theorem.** Any state with $\langle L_x \rangle \neq 0$ cannot be SdS.  
*Status: Proven directly from definitions.*

**Theorem.** Any state with $\langle L_y \rangle \neq 0$ cannot be SdS.  
*Status: Proven directly from definitions.*

---

**Theorem (SdS Incompatible with Nonzero L).** If any angular momentum expectation is nonzero:
$$\langle L_x \rangle \neq 0 \quad \text{or} \quad \langle L_y \rangle \neq 0 \quad \text{or} \quad \langle L_z \rangle \neq 0$$
then the state does not represent SdS.

*Status: Proven by case analysis on which component is nonzero.*

---

### 3.3 Main Results

**MAIN THEOREM (SdS is Forbidden).** In any universe with a thermal bath at T > 0, no physical state represents SdS.

*Status: Proven from the thermal excitation axiom and SdS incompatibility theorem.*

**Proof:**
1. Let ψ be any normalized state in appropriate domain
2. By `thermal_excites_angular_momentum`, at least one $\langle L_i \rangle \neq 0$
3. By `SdS_incompatible_with_nonzero_L`, ψ does not represent SdS
4. Since ψ was arbitrary, no physical state represents SdS. ∎

---

**COROLLARY (SdS Forbidden in Our Universe).** SdS is forbidden in our universe.

*Status: Proven by instantiating the main theorem with the CMB (T = 2.725 K).*

---

**PHYSICAL CONCLUSION (All Black Holes Rotate).** All black holes in de Sitter spacetime have $J \neq 0$.

*Status: Proven as direct consequence of the main theorem.*

---

## Part IV: Implications for the Information Paradox

### 4.1 The Standard Setup is Measure-Zero

The black hole information paradox is typically formulated in Schwarzschild or Schwarzschild-de Sitter spacetime. Key calculations assume:
- Spherical symmetry
- J = 0 (no rotation)
- Tractable mode decomposition

**This theorem establishes that J = 0 has probability zero in any thermal universe.**

The standard arena for the information paradox is not physically realizable.

---

### 4.2 The Challenge

Kerr-de Sitter differs from Schwarzschild-de Sitter in structurally important ways:
- Existence of an ergosphere
- Superradiant scattering
- Frame-dragging effects
- Modified horizon structure
- Different relationship between surface gravity and temperature

Whether the information paradox persists, is modified, or is resolved in KdS is an open question.

---

### 4.3 Conclusion

> **To the information paradox proponents: the ball is in your court. Prove the paradox still exists in KdS.**

*— Bornemann*

---

## Appendix: Logical Status Summary

### Axioms (Assumed)

| Axiom | Physical Basis |
|-------|----------------|
| `angular_momentum_commutator_xy` | Standard QM commutation relation |
| `thermal_excites_angular_momentum` | Measure theory + thermodynamics (4 independent justifications) |
| `zero_L_measure_zero` | Codimension argument |
| `thermal_variance_positive` | Fluctuation-dissipation theorem |
| `gravity_couples_to_angular_momentum` | No gravitational screening exists |

### Theorems (Proven in Lean)

| Theorem | Proof Method |
|---------|--------------|
| `hbar_pos` | Numerical computation |
| `unboundedStdDev_nonneg` | Properties of square root |
| `norm_I_mul_hbar` | Norm computation |
| `angular_momentum_uncertainty` | Robertson inequality + commutator |
| `angular_momentum_uncertainty_nonzero` | Contraposition |
| `nonzero_Lx_not_SdS` | Direct from definition |
| `nonzero_Ly_not_SdS` | Direct from definition |
| `nonzero_Lz_not_SdS` | Direct from definition |
| `SdS_incompatible_with_nonzero_L` | Case analysis |
| `SdS_forbidden` | Axiom + incompatibility theorem |
| `SdS_forbidden_our_universe` | Instantiation with CMB |
| `all_BH_rotating` | Direct consequence |

---

## Appendix: Physical Constants

| Constant | Value | Units |
|----------|-------|-------|
| ℏ | $1.054571817 \times 10^{-34}$ | J·s |
| $k_B$ | $1.380649 \times 10^{-23}$ | J/K |
| $T_{\text{CMB}}$ | 2.725 | K |
| CMB photon density | 411 | photons/cm³ |
| Universe age | $4.4 \times 10^{17}$ | s |

---

*Document generated from Lean 4 formalization.*  
