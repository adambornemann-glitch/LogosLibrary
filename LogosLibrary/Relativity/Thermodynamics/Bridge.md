# The Modular Origin of Thermodynamic Gravity

**Bridging Jacobson (1995) and Connes-Rovelli (1994) through Bisognano-Wichmann**

---

## The Punchline

In 1995, Ted Jacobson derived the Einstein field equations by demanding δQ = TdS at every local Rindler horizon. The temperature T and entropy S in this relation are not properties of a thermal system being boosted. They are properties of the **vacuum state restricted to a Rindler wedge**, determined entirely by the modular structure of that state via the Bisognano-Wichmann theorem.

In 1994, Alain Connes and Carlo Rovelli proposed that physical time emerges from the modular automorphism group of a von Neumann algebra: given a faithful state ω, the Tomita-Takesaki theorem provides a canonical one-parameter flow σ_τ, and this flow **is** time.

These are the same structure.

Jacobson's derivation implicitly applies Connes-Rovelli thermal time locally at every spacetime point, for every null direction. The Einstein equation emerges as the **integrability condition**: the requirement that all these local modular flows—one for each local Rindler horizon—are mutually consistent with a single smooth spacetime geometry.

The bridge between these programs is not a new argument. It is a theorem that already exists: Bisognano-Wichmann (1976), which proves that the modular flow of the Minkowski vacuum restricted to a Rindler wedge is the boost flow, with KMS temperature ℏ/(2π).

---

## 1. The Modular Core of Jacobson's Derivation

### 1.1 What Jacobson Actually Uses

The 1995 paper uses language about "an accelerated observer just inside the horizon" perceiving an "Unruh temperature." This is pedagogically helpful but potentially misleading. The conceptual framework does not depend on any particular observer's experience.

The actual ingredients are:

**The state:** The Minkowski vacuum |0⟩. This state is Poincaré invariant—it is the same state for all inertial observers.

**The algebra:** At any spacetime point p, for any null direction, there is a local Rindler wedge. The quantum field observables localized to this wedge form a von Neumann algebra M.

**The restriction:** The vacuum restricted to M defines a faithful normal state ω on M.

**Bisognano-Wichmann (1976):** The modular automorphism group σ_τ of ω with respect to M is the one-parameter group of Lorentz boosts preserving the wedge. The vacuum restricted to the wedge is a KMS state at inverse temperature β = 2π/ℏ (in units where k_B = 1) with respect to the boost Hamiltonian H_B:

$$\rho_{\text{wedge}} \sim \exp\!\left(-\frac{2\pi}{\hbar}\, H_B\right)$$

**The "temperature":** The quantity ℏ/(2π) that appears here has dimensions of action, not energy. It is a fixed constant determined by the modular structure. It does not transform under Lorentz boosts because the vacuum state itself is Lorentz invariant.

**The Clausius relation:** Jacobson demands that when energy flux δQ crosses a local Rindler horizon, the relation δQ = TdS holds, where T = ℏ/(2π) is the modular temperature and dS = δA/(4ℓ_P²) is the entropy change from the Bekenstein-Hawking area law.

**The result:** This local thermodynamic equilibrium condition, imposed at every point for every null direction, forces the geometry to satisfy:

$$G_{\mu\nu} = \frac{8\pi G}{c^4}\, T_{\mu\nu}$$

### 1.2 What Jacobson Does Not Use

Jacobson's derivation does **not** involve:

- Boosting a thermal system and asking how its temperature transforms
- The Ott transformation T → γT
- Any observer-dependent temperature
- Any frame-dependent thermodynamic quantity

The entire construction is built from Lorentz-invariant objects: the vacuum state, the modular structure, the KMS condition. The covariance of the Einstein equation emerges because the construction is the same at every point for every observer—not because thermodynamic quantities transform in a particular way under boosts.

---

## 2. The Connes-Rovelli Thermal Time Hypothesis

### 2.1 The Proposal

In generally covariant quantum theories, there is no preferred time variable. The Hamiltonian is a constraint (H ≈ 0), not a generator of dynamics. Time appears to be frozen.

Connes and Rovelli's resolution: given any faithful state ω on a von Neumann algebra M, the Tomita-Takesaki theorem provides a canonical one-parameter automorphism group σ_τ—the modular flow. The thermal time hypothesis identifies this flow with physical time evolution:

$$t = \frac{\hbar}{2\pi k_B} \cdot \frac{\tau}{T}$$

where τ is the modular parameter and T is the temperature characterizing the state.

### 2.2 The Key Properties

The modular flow has several remarkable properties:

1. **Existence:** It is guaranteed by pure mathematics (Tomita-Takesaki theorem) for any faithful normal state on a von Neumann algebra. No Hamiltonian is needed.

2. **State-dependence:** Different states give different flows. Time depends on the thermodynamic state of the system.

3. **Physical content:** For known physical systems, the modular flow reproduces the correct time evolution. For the vacuum in a Rindler wedge, it gives the boost flow (Bisognano-Wichmann). For a Gibbs state at temperature T, it gives time evolution generated by the Hamiltonian, rescaled by T.

4. **Cocycle invariance:** The Connes cocycle Radon-Nikodym theorem ensures that the outer automorphism class of the modular flow is state-independent. Changing the state changes the flow only by an inner automorphism—a physically trivial gauge transformation.

---

## 3. Bisognano-Wichmann: The Bridge

### 3.1 The Theorem

**Bisognano-Wichmann (1976):** Let M be the von Neumann algebra of observables localized in the right Rindler wedge W_R = {x : x¹ > |x⁰|}. Let ω be the Minkowski vacuum restricted to M. Then:

1. The modular operator is Δ = exp(-2π H_B / ℏ), where H_B is the boost generator.
2. The modular automorphism group σ_τ is the one-parameter group of boosts preserving W_R.
3. The modular conjugation J implements the CPT reflection mapping W_R to the left wedge W_L.

### 3.2 Why This Is the Bridge

Consider what Bisognano-Wichmann says from the two perspectives:

**From Connes-Rovelli's perspective:** The modular flow of the vacuum restricted to a Rindler wedge IS a geometric flow—the boost flow. The thermal time hypothesis says modular flow is time. In this case, the "time" is boost time, and the "temperature" is ℏ/(2π). This is a concrete realization of the thermal time program.

**From Jacobson's perspective:** The δQ = TdS relation at a local Rindler horizon uses T = ℏ/(2π) and identifies entropy change with area change. The T comes from exactly the modular structure that Bisognano-Wichmann identifies. The energy flux δQ is the expectation value of the boost Hamiltonian H_B applied to the perturbed state. The entire Clausius relation is a statement about the modular structure.

**The identification:** Jacobson's local thermodynamic equilibrium condition IS the statement that the vacuum state, restricted to each local Rindler wedge, satisfies the KMS condition with respect to the local boost flow. This is exactly the Connes-Rovelli thermal time hypothesis applied locally.

### 3.3 The 2π

The factor 2π appearing in the Unruh temperature T_U = ℏa/(2πk_B) and in the Einstein equation coefficient 8πG = 4 × 2π × G is not a convention. It is the periodicity of the modular automorphism group.

The KMS condition states that thermal correlation functions are periodic in imaginary time with period β = 1/T (in natural units). For the vacuum restricted to a Rindler wedge, β = 2π. This 2π is a theorem—a consequence of the algebraic structure—not a choice.

The factor of 4 in the Bekenstein-Hawking entropy S = A/(4ℓ_P²) combines with the 2π from modular periodicity to give 8π in the Einstein equation. Both factors are determined by the formalism.

---

## 4. The Einstein Equation as Integrability Condition

### 4.1 Local Modular Structures

At every spacetime point p, for every null direction n, there is a local Rindler horizon. The vacuum restricted to the corresponding local wedge has a modular structure: a modular flow, a KMS temperature, a modular Hamiltonian.

This gives a vast family of local modular data—one for each (p, n) pair.

### 4.2 The Consistency Requirement

These local modular structures are not independent. They are all derived from a single object: the vacuum state on a single spacetime. The requirement that all local structures be mutually consistent—that they all derive from a common global state on a common geometry—is a powerful constraint on the geometry.

**Jacobson's result:** This consistency requirement is equivalent to the Einstein field equations.

Stated differently: if you demand that the Connes-Rovelli thermal time hypothesis holds locally at every point, and that all local thermal times are compatible with a smooth global spacetime, you get general relativity.

### 4.3 The Analogy to Equations of State

Jacobson's famous observation is that this makes the Einstein equation an "equation of state"—analogous to the ideal gas law PV = NkT. Just as the gas law is not a fundamental equation to be quantized (you wouldn't quantize sound waves in air), the Einstein equation may not be a fundamental equation to be quantized either.

In the present language: the Einstein equation is the **integrability condition for a field of local modular structures**. It ensures that the local thermal time flows at every point can be embedded in a single consistent spacetime. It is an emergent, thermodynamic relation, not a fundamental dynamical law.

This is the deepest point of contact with Connes-Rovelli. Their program says time is modular flow. Jacobson's result says that demanding local modular consistency—local thermal equilibrium everywhere—forces Einstein's equation. Together:

> **Spacetime geometry is the structure that makes local thermal time globally consistent.**

---

## 5. The Problem of Time

### 5.1 The Problem

In canonical quantum gravity, the Hamiltonian is a constraint:

$$H|\psi\rangle = 0$$

If H generates time evolution, then ∂|ψ⟩/∂t = 0. Nothing happens. Time is frozen.

### 5.2 The Resolution

The modular flow σ_τ is constructed from the state ω by the Tomita-Takesaki theorem. It requires:

- A von Neumann algebra M
- A faithful normal state ω on M

It does **not** require a Hamiltonian. The Tomita operator S is defined by:

$$S \, A\Omega = A^* \Omega$$

where Ω is the GNS vector for ω and A ∈ M. The polar decomposition S = JΔ^{1/2} defines the modular operator Δ, and the modular flow is:

$$\sigma_\tau(A) = \Delta^{i\tau} A \, \Delta^{-i\tau}$$

This exists and defines a one-parameter automorphism group regardless of whether any Hamiltonian constraint is satisfied.

For thermal states where a Hamiltonian exists, the modular Hamiltonian K is related to H by K = H/T. When H ≈ 0 as a constraint, the modular flow still exists—it is defined by the state, not by H. The state encodes all the physical information, and the modular flow extracts the temporal structure from it.

### 5.3 The Connection to Jacobson

In Jacobson's framework, the local dynamics at each Rindler horizon are generated by the local boost Hamiltonian H_B via the modular structure. The boost Hamiltonian is NOT the total Hamiltonian of the gravitational theory (which vanishes as a constraint). It is a local, wedge-specific generator defined by the modular structure of the vacuum.

The constraint H ≈ 0 is a global statement about the total theory. The modular flow σ_τ is a local statement about the state restricted to a subsystem. There is no conflict. The global Hamiltonian vanishes, but the local modular generators—one for each horizon—are nontrivial and generate real dynamics.

This is how time survives in a theory with H ≈ 0: not through the global Hamiltonian, but through the local modular structures at every horizon.

---

## 6. Where Ott Lives

### 6.1 What Ott Is About

The Ott transformation T → γT describes how the temperature of a **physical thermal system** transforms when you boost it. A box of gas at temperature T, viewed by an observer moving at velocity v, has temperature γT.

This is a correct result about actual thermal systems. It is proven by seven independent arguments (see companion document: *The Ott Temperature Transformation: A Definitive Resolution*).

### 6.2 What Ott Is Not About

Ott does not play a role in Jacobson's derivation because Jacobson's derivation does not involve boosting a thermal system. The "temperature" in Jacobson's framework is the modular temperature ℏ/(2π) of the vacuum restricted to a local Rindler wedge. This is not a physical thermal system being viewed from a different frame—it is a fixed algebraic property of the vacuum state.

A Lorentz boost does not change the vacuum state (it is Poincaré invariant). It maps one Rindler wedge to another, but each wedge has the same modular structure with the same temperature ℏ/(2π). There is nothing for Ott to transform.

### 6.3 Where Ott Does Apply

Ott becomes relevant when considering:

- **Actual thermal states** (not the vacuum): A gas at temperature T, a black body, a plasma. These are physical systems whose temperature transforms under boosts.
- **Black hole thermodynamics for boosted observers:** An observer falling toward a black hole at velocity v relative to a stationary observer at infinity sees a Hawking temperature T' = γT_H. This is a genuine Ott transformation of a physical thermal system.
- **The uniqueness of thermal time:** The companion document (*The Uniqueness of Thermal Time*) proves that t = cτ/T is the unique Lorentz-covariant thermal time relation, using Ott as an input. This result is correct and stands on its own, but it concerns the behavior of thermal time under boosts of thermal systems—a different physical situation from Jacobson's vacuum-based derivation.

### 6.4 The Relationship

Ott and the modular temperature ℏ/(2π) are not in conflict. They live at different levels:

- **ℏ/(2π):** The modular temperature of the vacuum restricted to any Rindler wedge. Fixed. Algebraic. Does not transform.
- **T → γT (Ott):** The transformation law for the temperature of a physical thermal state under boosts. Dynamic. Physical. Transforms covariantly.

When you have a physical thermal state at temperature T and restrict to a Rindler wedge, the full modular structure involves both T and the geometric factor ℏ/(2π). The Ott transformation governs how T changes. The modular period 2π does not change. The interplay between these is governed by the KMS condition.

---

## 7. The Unity

### Three Programs, One Structure

| Program | Key Object | Key Insight |
|---------|-----------|-------------|
| Connes-Rovelli (1994) | Modular flow σ_τ | Time IS modular flow |
| Jacobson (1995) | δQ = TdS at local horizons | Geometry IS thermodynamic equilibrium |
| Bisognano-Wichmann (1976) | Δ = exp(-2πH_B/ℏ) | Modular flow of vacuum IS boost flow |

The relationships:

- **Bisognano-Wichmann realizes Connes-Rovelli** for the specific case of the vacuum in a Rindler wedge: the modular flow is the boost, and thermal time is boost time.

- **Jacobson applies this realization locally** at every spacetime point, for every null direction. Each local horizon carries a local Connes-Rovelli thermal time.

- **The Einstein equation** is the condition that all these local thermal times are globally consistent—that the local modular structures fit together into a smooth spacetime.

### The Logical Structure

```
Tomita-Takesaki theorem
    (modular flow exists for any faithful state)
                    ↓
Bisognano-Wichmann theorem
    (vacuum modular flow = boost flow, T = ℏ/2π)
                    ↓
Jacobson's local equilibrium condition
    (δQ = TdS at every local Rindler horizon)
                    ↓
Einstein field equations
    (integrability condition for local modular structures)
```

Connes-Rovelli's thermal time hypothesis provides the conceptual framework: time is modular flow. Bisognano-Wichmann provides the concrete realization: for the vacuum, modular flow is geometric. Jacobson provides the dynamical consequence: consistency of local modular flows forces Einstein's equation.

### What Has Been Formalized

The Lean 4 formalization provides machine-verified proofs of:

- `thermalTime_unique`: The thermal time relation t = cτ/T is the unique Lorentz-covariant form (for thermal systems where Ott applies)
- `modular_hamiltonian_invariant`: K = H/T is a Lorentz scalar (for thermal systems)
- `rindler_thermodynamics_covariant`: The Clausius relation transforms correctly under Ott (for thermal systems)
- `unruh_from_modular_period`: The 2π in the Unruh temperature is the modular period
- `thermal_time_gives_time_dilation`: Time dilation emerges from thermal time + Ott (for thermal systems)

The bridge itself—the identification of Jacobson's local thermodynamics with Connes-Rovelli thermal time via Bisognano-Wichmann—is a conceptual identification, not a formal theorem. It rests on the mathematical fact (Bisognano-Wichmann) that the modular structure of the vacuum is the boost structure, and on the physical identification (Jacobson) of the Clausius relation with this modular structure.

### What Remains to Formalize

The full formalization of the bridge requires:

1. **Bisognano-Wichmann in Lean 4:** The modular operator of the vacuum restricted to a Rindler wedge equals exp(-2πH_B/ℏ).
2. **Local Rindler wedge construction:** At each spacetime point, for each null direction, the local wedge and its algebra.
3. **Jacobson's derivation:** From local KMS equilibrium to the Raychaudhuri equation to the Einstein equation.
4. **Integrability:** The precise sense in which the Einstein equation is the consistency condition for local modular structures.

These are substantial formalizations requiring the full Tomita-Takesaki theory in Lean 4.

---

## 8. Conclusion

Jacobson's 1995 derivation of the Einstein equation from thermodynamics is, at its core, a demonstration that general relativity emerges from the modular structure of the quantum vacuum. The temperature in the derivation is not an observer-dependent quantity that transforms under boosts—it is the fixed modular temperature ℏ/(2π) determined by the Bisognano-Wichmann theorem.

This places the derivation squarely within the Connes-Rovelli thermal time program. Both frameworks assert that the fundamental physical content is carried by the modular structure of quantum states, not by a classical Hamiltonian. In Connes-Rovelli, this insight resolves the problem of time. In Jacobson, it derives the Einstein equation.

The Ott temperature transformation (T → γT) governs the distinct physical situation of boosting actual thermal systems. It is correct, well-established, and relevant to black hole thermodynamics and relativistic statistical mechanics. But it is not the mechanism by which Jacobson's derivation achieves covariance. That covariance comes from the Poincaré invariance of the vacuum state itself.

The three programs—Connes-Rovelli's thermal time, Jacobson's thermodynamic gravity, and the Bisognano-Wichmann identification of modular and geometric structure—are not three ideas. They are one idea, viewed from three angles:

> **The Einstein equation is what you get when you demand that Connes-Rovelli thermal time, realized locally via Bisognano-Wichmann, is globally consistent.**

---

## References

[1] T. Jacobson, "Thermodynamics of Spacetime: The Einstein Equation of State," Phys. Rev. Lett. **75**, 1260 (1995). [arXiv:gr-qc/9504004]

[2] A. Connes, C. Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics relation in generally covariant quantum theories," Class. Quantum Grav. **11**, 2899 (1994). [arXiv:gr-qc/9406019]

[3] J.J. Bisognano, E.H. Wichmann, "On the Duality Condition for a Hermitian Scalar Field," J. Math. Phys. **16**, 985 (1975).

[4] J.J. Bisognano, E.H. Wichmann, "On the Duality Condition for Quantum Fields," J. Math. Phys. **17**, 303 (1976).

[5] T. Jacobson, "Entanglement Equilibrium and the Einstein Equation," Phys. Rev. Lett. **116**, 201101 (2016). [arXiv:1505.04753]

[6] T. Jacobson, "On the nature of black hole entropy," in *General Relativity and Relativistic Astrophysics*, AIP Conf. Proc. **493**, 85 (1999). [arXiv:gr-qc/9908031]

[7] T. Jacobson, R. Parentani, "Horizon Entropy," Found. Phys. **33**, 323 (2003). [arXiv:gr-qc/0302099]

[8] R. Haag, *Local Quantum Physics*, Springer (1996).

[9] H. Ott, "Lorentz-Transformation der Wärme und der Temperatur," Z. Physik **175**, 70 (1963).

[10] T. Jacobson, "Black Hole Thermodynamics and Lorentz Symmetry," Found. Phys. **40**, 1076 (2010). [arXiv:0905.4051]

---

*Formalization status: Conceptual bridge document. Supporting Lean 4 proofs in companion files. Full formalization pending Bisognano-Wichmann and Tomita-Takesaki in Lean 4.*

*— A. Bornemann, 2026*
