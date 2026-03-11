# Superior-String Theory

**A formally verified framework for QCD flux tube strings with emergent time**

*Adam Bornemann, 2026*

---

## What This Is

This is a mathematical physics framework, written in Lean 4 and
machine-checked against Mathlib, that treats QCD flux tubes as
fundamental strings in **three spatial dimensions** with time
emerging from Tomita–Takesaki modular flow.

The entire framework is derived from a single parameter: the
string tension σ > 0.

"Formally verified" means: every theorem has a complete proof that
has been checked by a computer. There are no gaps, no "it can be
shown that," no arguments by analogy. The machine accepts the proof
or it doesn't. Zero `sorry` (Lean's marker for an incomplete proof)
appears in the synthesis.

---

## The Physical Picture

### The Problem with Standard String Theory

Standard bosonic string theory embeds time as a target-space
coordinate and obtains a critical spacetime dimension D = 26
(or D = 10 for the superstring) from Weyl anomaly cancellation.
This has never made contact with QCD.

Meanwhile, lattice QCD observes that the static quark–antiquark
potential at large separation R is

$$V(R) \;=\; \sigma R \;-\; \frac{\pi}{12R} \;+\; \cdots$$

The second term is the **Lüscher term**: the Casimir energy of
transverse fluctuations of the chromoelectric flux tube connecting
the quarks. Lattice simulations measure the coefficient to be
−π/12, corresponding to **two transverse modes**.

The standard interpretation is: 4 spacetime dimensions minus 2
(time + longitudinal) = 2 transverse modes.

### The Entropic Reinterpretation

This framework offers a different counting:

> **Time is not a target-space dimension.**
> **Time is the modular flow parameter σ_R from Tomita–Takesaki theory.**

The target space is purely spatial, with **D_spatial = 3**.
Subtracting 1 longitudinal direction gives 2 transverse modes.
Same Lüscher coefficient. Same physics. Different ontology.

The entropic parameter is a quaternion:

$$\varsigma \;=\; \sigma_R + \mathbf{i}\,\sigma_I + \mathbf{j}\,\sigma_J + \mathbf{k}\,\sigma_K$$

where:
- σ_R ∈ ℝ is the **entropy flow** (generates physical time)
- σ_I parametrizes the **thermal circle** S¹ (KMS periodicity)
- (σ_J, σ_K) parametrize the **angular momentum sphere** S²

This decomposition is not ad hoc — it is the **Hopf fibration**
S¹ ↪ S³ → S², applied to the unit quaternions.

---

## The Architecture

The framework is organized across five files, each proving a
self-contained set of results, culminating in a single master
theorem with no unfinished proofs.

```
Superior/Strings/
├── Basic.lean          QCD string parameters, Lüscher term, hierarchy
├── Thermal.lean        Lorentz covariance of entropic time
├── Topology.lean       Hopf fibration, S¹ fiber, single axion
├── Quaternion.lean     su(2) algebra, Fueter operator, conjugation action
└── Synthesis.lean      The master theorem (10 results, 0 sorry)
```

---

## The Ten Results

All ten are proved simultaneously in `Synthesis.lean`. Here they
are in physicist notation, with pointers to where the formal proofs
live.

### (1) Critical Dimension: D_spatial = 3

The target space has three spatial dimensions. Time is not among
them. This is the starting axiom of the framework, and the Lüscher
term (result 2) serves as its consistency check.

> `Basic.lean → D_spatial_eq`

### (2) Lüscher Coefficient = −π/12

The static potential Casimir term is

$$E_{\text{Casimir}} \;=\; -\frac{\pi(D_s - 1)}{24R}$$

With D_s = 3, this gives −π·2/24 = **−π/12**, matching lattice
QCD measurements.

The standard framework obtains the same number via (D − 2)/24
with D = 4 spacetime dimensions. The two countings agree because
both give 2 transverse modes.

> `Basic.lean → luescher_coefficient_value`

### (3) Gravitational Hierarchy: G_eff · σ = 2√3

The framework defines an effective gravitational coupling G_eff by
requiring that the **entropic temperature** (from modular flow)
equals the **Hagedorn temperature** (from the string spectrum):

$$T_{\text{entropic}} = \frac{G_{\text{eff}}\, m^2}{2\pi\,\Delta x} \;=\; \frac{\sqrt{3\sigma}}{\pi} = T_H$$

With m = √σ and Δx = 1/√σ, solving for G_eff gives

$$G_{\text{eff}} \;=\; \frac{2\sqrt{3}}{\sigma}$$

The hierarchy ratio to Newton's constant is then

$$\frac{G_{\text{eff}}}{G_N} \;=\; \frac{2\sqrt{3}\,M_P^2}{\sigma} \;\sim\; 10^{38}$$

This contains **no free parameters** beyond the QCD and Planck
scales. The product G_eff · σ = 2√3 is universal across all QCD
strings.

> `Basic.lean → QCDString.G_eff_times_σ`
> `Basic.lean → GravitationalHierarchy.hierarchy_ratio`

### (4) Conjugacy: τ_C · T = 1/(2π)

The collapse timescale τ_C = Δx/(G m²) and the entropic
temperature T = G m²/(2π Δx) satisfy

$$\tau_C \cdot T \;=\; \frac{1}{2\pi}$$

This is the thermodynamic avatar of the energy–time uncertainty
relation. The two quantities are conjugate: knowing one precisely
determines the other.

Physical time emerges as dt = τ_C · dσ_R, and one full KMS cycle
(σ_R advances by 2π) gives a physical time interval of exactly
1/T.

> `Basic.lean → collapse_temperature_identity`
> `Basic.lean → one_cycle_gives_inverse_temperature`

### (5) Lorentz Covariance: K′ = K

The modular Hamiltonian K = H/T is **Lorentz invariant**.

Under a boost with Lorentz factor γ, the energy transforms as
H → γH (standard) and the temperature transforms as T → γT
(Ott transformation). Their ratio is unchanged:

$$K' \;=\; \frac{\gamma H}{\gamma T} \;=\; \frac{H}{T} \;=\; K$$

The Ott transformation — not the Planck–Einstein T → T/γ — is
the correct relativistic temperature law in this framework. The
key insight is that temperature transforms as energy because the
localization scale Δx Lorentz-contracts:

$$T' = \frac{G m^2}{2\pi\,\Delta x'} = \frac{G m^2}{2\pi\,\Delta x/\gamma} = \gamma T$$

> `Thermal.lean → modular_hamiltonian_invariant`
> `Thermal.lean → entropic_temperature_transforms_ott`

### (6) Emergent Time Dilation: t′ = t/γ

Time dilation is **not postulated**. It is derived from two
ingredients:

1. The Ott transformation: T′ = γT
2. The thermal time hypothesis: t = σ_R/T

Together: t′ = σ_R/(γT) = t/γ.

Special relativity emerges from thermodynamics + modular theory.

> `Thermal.lean → entropic_time_dilation`

### (7) Entropy Invariance: σ_R′ = σ_R

The entropy flow parameter σ_R is a **Lorentz scalar**. All
inertial observers agree on how much entropy has flowed.

This follows from the cancellation: if t = τ_C · σ_R, and both
t and τ_C pick up the same factor of 1/γ under a boost, then
σ_R = t/τ_C is invariant.

Physically: σ_R counts bits. Counts don't Lorentz-transform.

> `Thermal.lean → entropy_flow_invariant`

### (8) Single Axion from the Hopf Fiber

The quaternionic entropic parameter lives on S³ (the unit
quaternions). The Hopf fibration

$$S^1 \;\hookrightarrow\; S^3 \;\xrightarrow{\;\pi\;}\; S^2$$

decomposes S³ into an S¹ fiber (the thermal circle) over an S²
base (angular momentum directions).

The key theorem: the S¹ rotation **preserves the Hopf projection**.
Rotating the fiber changes the quaternion but not the image on S².
This is proved by explicit computation:

$$\pi(e^{i\theta} \cdot q) \;=\; \pi(q) \quad\text{for all } \theta$$

The axion winding number lives in π₁(S¹) = ℤ: exactly **one
independent winding mode**. Not three (which would require
nontrivial π₁(S³)), not zero. One. This matches lattice QCD.

> `Topology.lean → fiber_preserves_hopf`
> `Topology.lean → hopf_maps_sphere_to_sphere`
> `Topology.lean → hopf_surjective`

### (9) Quaternion Algebra = su(2)

The imaginary quaternion commutators are verified:

$$[\mathbf{i}, \mathbf{j}] = 2\mathbf{k}, \qquad [\mathbf{j}, \mathbf{k}] = 2\mathbf{i}, \qquad [\mathbf{k}, \mathbf{i}] = 2\mathbf{j}$$

These **are** the su(2) structure constants (with the physics
convention J_a = σ_a/2). The Jacobi identity is proved, confirming
that pure imaginary quaternions form a Lie algebra.

The Hopf map from result (8) is identified with the **conjugation
action**: π(q) = q · **i** · q̄. This connects the topological
structure (fiber, base, winding) to the algebraic structure
(rotations, angular momentum).

Additionally, the full quaternion product of two pure imaginary
quaternions decomposes as:

$$\mathbf{p}\,\mathbf{q} \;=\; -(\mathbf{p} \cdot \mathbf{q}) \;+\; (\mathbf{p} \times \mathbf{q})$$

The dot product and cross product of ℝ³ are **not independent
operations** — they are the real and imaginary parts of a single
quaternion multiplication.

> `Quaternion.lean → comm_qi_qj, comm_qj_qk, comm_qk_qi`
> `Quaternion.lean → jacobi_identity`
> `Quaternion.lean → hopf_is_conjugation_component`
> `Quaternion.lean → fiber_preserves_conjugation`

### (10) Fueter–Laplacian Identity: ∂̄*∂̄ = Δ₄

The Fueter operator

$$\bar{\partial} \;=\; \frac{\partial}{\partial\sigma_R} + \mathbf{i}\frac{\partial}{\partial\sigma_I} + \mathbf{j}\frac{\partial}{\partial\sigma_J} + \mathbf{k}\frac{\partial}{\partial\sigma_K}$$

is the quaternionic generalization of the Cauchy–Riemann operator
∂/∂z̄. At the symbol level, its conjugate composed with itself gives

$$\tilde{\sigma}^* \cdot \tilde{\sigma} \;=\; (\sigma_0^2 + \sigma_1^2 + \sigma_2^2 + \sigma_3^2, \; 0, \; 0, \; 0)$$

The real part is the **4D Laplacian symbol**. All imaginary parts
vanish — the Laplacian is a **scalar operator** that does not mix
quaternionic components. This is a nontrivial algebraic identity
verified by `ring`.

The quaternionic evolution equation ∂̄ψ = (source) is therefore
**elliptic** and well-posed. The Fueter symbol is identified with
the entropic quaternion: the differential operator IS the
algebraic structure.

> `Quaternion.lean → fueter_laplacian_complete`
> `Quaternion.lean → fueter_is_entropic`

---

## What "Formally Verified" Means

Every theorem in this library has a **complete, machine-checked
proof**. The Lean 4 proof assistant, together with the Mathlib
mathematical library, verifies each logical step. The verification
is not probabilistic or approximate — it is absolute within the
foundational system (dependent type theory).

Concretely:

| Claim | Status |
|:------|:-------|
| All algebraic identities (Hopf norm, quaternion products, field_simp results) | Machine-checked |
| Positivity and well-definedness of all physical quantities | Machine-checked |
| Lorentz covariance (all γ-cancellations) | Machine-checked |
| Topological structure (fiber preservation, norm preservation, surjectivity) | Machine-checked |
| Lie algebra structure (commutators, Jacobi identity) | Machine-checked |
| π₁(S¹) = ℤ, π₁(S³) = 0 (standard algebraic topology) | Axiomatized |

The axiomatized facts (homotopy groups of spheres, Hurwitz's
theorem) are standard results from algebraic topology and abstract
algebra. They are not yet in Mathlib and are marked as `axiom`
declarations. Everything conditional on them is fully verified.

**What this does not verify:**

The physical *interpretation* — that time is modular flow, that
the correct dimension counting is D_spatial rather than
D_spacetime, that G_eff should be defined by T_entropic = T_H —
is not something a proof assistant can check. These are physical
hypotheses. What the machine confirms is that the mathematical
consequences are internally consistent and correctly derived.

---

## The Dependency Structure

```
ThermalTime/Basic.lean          Thermal time, Ott transformation
         │
         ▼
Relativity/LorentzBoost/Ott.lean    Lorentz factor, γ ≥ 1
         │
         ├──────────────────────────────┐
         ▼                              ▼
  Strings/Basic.lean            Strings/Thermal.lean
  (σ, m, Δx, Lüscher,          (Ott covariance, τ_C
   G_eff, τ_C·T = 1/2π)         dilation, σ_R invariant)
         │                              │
         │    ┌─────────────────────────┘
         │    │
         │    │    Strings/Topology.lean        Strings/Quaternion.lean
         │    │    (Hopf map, S¹ fiber,         (su(2), Fueter, conj.
         │    │     axion, division algebras)    action, Hopf connection)
         │    │           │                              │
         ▼    ▼           ▼                              ▼
         ┌────────────────────────────────────────────────┐
         │          Strings/Synthesis.lean                │
         │     The master theorem: 10 results, 0 sorry    │
         └────────────────────────────────────────────────┘
```

---

## Key Physical Relationships

For reference, the core equations in one place. Every relation
below is proved in the library.

**String scales** (from σ alone):

$$m = \sqrt{\sigma}, \qquad \Delta x = \frac{1}{\sqrt{\sigma}}, \qquad m \cdot \Delta x = 1$$

**Effective gravitational coupling:**

$$G_{\text{eff}} = \frac{2\sqrt{3}}{\sigma}, \qquad G_{\text{eff}} \cdot \sigma = 2\sqrt{3}$$

**Temperatures:**

$$T_H = \frac{\sqrt{3\sigma}}{\pi}, \qquad T_{\text{entropic}} = \frac{G_{\text{eff}}\,\sigma^{3/2}}{2\pi}$$

**Time–temperature conjugacy:**

$$\tau_C = \frac{\Delta x}{G_{\text{eff}}\,m^2}, \qquad \tau_C \cdot T = \frac{1}{2\pi}$$

**Lorentz transformations (Ott):**

$$T' = \gamma T, \qquad \tau_C' = \tau_C/\gamma, \qquad \sigma_R' = \sigma_R, \qquad K' = K$$

**Hopf fibration:**

$$\pi(a,b,c,d) = \big(2(ac+bd),\; 2(bc-ad),\; a^2+b^2-c^2-d^2\big)$$

$$|\pi(q)|^2 = |q|^4 \qquad\Rightarrow\qquad q \in S^3 \;\Longrightarrow\; \pi(q) \in S^2$$

---

## Open Questions

This framework is **kinematic**, not dynamic. The following are
not yet addressed and represent the path forward:

1. **Scattering amplitudes.** No S-matrix has been derived.
   A Lean-verified derivation of even a simple 2→2 amplitude
   would constitute significant progress.

2. **Anomaly cancellation.** Standard string theory derives
   D = 26 (or 10) from Weyl anomaly cancellation on the
   worldsheet. What is the analogous consistency condition that
   *forces* D_spatial = 3 in this framework?

3. **Lattice predictions.** The Lüscher term is a retrodiction.
   What does the framework predict that lattice QCD has not yet
   measured? The single-axion claim and universal axion
   phenomenology across SU(2) and SU(3) are candidates.

4. **Dynamical G_eff.** The identification T_entropic = T_Hagedorn
   defines G_eff. Can this be derived from a more fundamental
   principle, rather than imposed?

5. **Octonionic extension.** The Hopf tower suggests
   S⁷ ↪ S¹⁵ → S⁸ for the octonions. The division algebra
   hierarchy (ℝ, ℂ, ℍ, 𝕆) ↔ (trivial, U(1), SU(2), SU(3))
   is conjectural. Formalizing it would connect the framework
   to the Standard Model gauge group.

---

## Building

Requires Lean 4 and Mathlib. The framework additionally depends on
`LogosLibrary.Relativity.Thermodynamics.Ott` and
`LogosLibrary.Superior.ThermalTime.Basic` from the parent library.

---

## The Ledger

| | |
|:---|:---|
| **Axioms used** | 0 (in synthesis; 3 standard topology facts axiomatized in Topology.lean) |
| **Sorry count** | 0 |
| **Free parameters** | 0 (everything from σ) |
| **Spatial dimensions** | 3 (time emerges) |
| **Axions** | 1 (from S¹ fiber) |
| **Files** | 5 |
| **Theorems in synthesis** | 10 |


∎
