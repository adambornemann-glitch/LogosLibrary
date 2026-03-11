# Information Geometry and Tighter Decoherence Bounds

**A roadmap for applying the Amari–Chentsov structure to the E-Process collapse rate**

*Notes from March 2026*

---

## 1. The Current Bound

The E-Process (`EProcess.lean`) proves that after one complete modular cycle (2π nats of entropy production), off-diagonal coherence is suppressed by a factor of

$$\rho_{\text{off}} \to e^{-2\pi}\,\rho_{\text{off}}$$

The formalization establishes:

$$e^{-2\pi} < 0.003$$

meaning coherence is reduced to less than 0.3% of its initial value. The exact value is $e^{-2\pi} \approx 0.001867$, so the bound is already fairly tight numerically.

The question is whether **information geometry** — specifically, the curvature of the quantum statistical manifold — can tighten the **physics**, not just the numerics.

The answer is **yes**, and the mechanism is geodesic curvature on the Bures manifold.

---

## 2. Why the Current Model Underestimates Decoherence

The current collapse rate model uses exponential decay of the Lindblad form:

$$\frac{\partial \rho_{\text{off}}}{\partial \sigma} = -\tilde{\Gamma}(\Delta s)\,\rho_{\text{off}}$$

which gives the solution $\rho_{\text{off}}(\sigma) = e^{-\tilde{\Gamma}\sigma}\,\rho_0$.

This is a **first-order, flat-space** approximation. It treats the decoherence trajectory as a straight line in state space — a constant-rate exponential decay parameterized by the entropic time $\sigma$.

But the space of quantum states is **not flat**. It is a Riemannian manifold equipped with the Bures metric (equivalently, the quantum Fisher information metric in the SLD sense). Straight-line estimates on curved manifolds systematically **undercount** the actual geodesic distance traversed.

The key insight from information geometry: **decoherence is geodesic motion on a curved statistical manifold**, and the curvature correction makes decoherence *faster* than the flat estimate predicts.

---

## 3. The Bures Metric Is the Quantum Fisher Metric

The Bures distance between two quantum states $\rho$ and $\sigma$ is:

$$d_B(\rho, \sigma) = \arccos\!\left(\mathrm{Tr}\sqrt{\sqrt{\rho}\,\sigma\,\sqrt{\rho}}\right)$$

This is the **geodesic distance** on the manifold of density matrices. It is related to the quantum fidelity $F(\rho, \sigma)$ by $d_B = \arccos\sqrt{F}$.

The infinitesimal form of the Bures metric is:

$$ds^2_B = \frac{1}{4}\,F_Q[\rho, d\theta]\,d\theta^2$$

where $F_Q$ is the **quantum Fisher information** (symmetric logarithmic derivative, or SLD, metric). This is the unique monotone metric in the Petz classification corresponding to the operator mean $c(x,y) = \frac{x+y}{2}$.

The identification:

| Object | Information geometry name | Quantum mechanics name |
|--------|--------------------------|------------------------|
| State space | Statistical manifold $\mathcal{D}_n^+$ | Space of faithful density matrices |
| Metric | SLD Fisher information | Bures metric (infinitesimal) |
| Geodesic distance | Canonical divergence (Hessian) | Bures distance |
| $\alpha = +1$ connection | $e$-connection | Exponential family structure |
| $\alpha = -1$ connection | $m$-connection | Mixture family structure |

The E-Process Lindblad decay corresponds to motion along an **$m$-geodesic** (mixture connection), which is a straight line in mixture coordinates. The Bures geodesic (Levi-Civita, $\alpha = 0$) is shorter.

---

## 4. The Curvature Correction

On a Riemannian manifold with scalar curvature $\kappa$ at a point, the geodesic ball of radius $r$ has volume:

$$\mathrm{Vol}(B_r) = \omega_n\,r^n\left(1 - \frac{\kappa}{6(n+2)}\,r^2 + \mathcal{O}(r^4)\right)$$

where $\omega_n$ is the flat-space volume. For **negative** curvature ($\kappa < 0$), geodesic balls are **larger** than their flat-space counterparts — distances grow faster than the flat estimate.

The Bures manifold of $n \times n$ density matrices has **non-positive sectional curvature** in directions associated with decoherence (loss of off-diagonal elements). This means:

- The actual geodesic distance from a coherent state to its decohered version is **larger** than the coordinate distance estimated by the Lindblad exponential.
- Equivalently, reaching a given Bures distance (a given level of distinguishability between the coherent and decohered states) requires **less** entropic time than the flat estimate suggests.
- **Decoherence is faster than $e^{-\tilde{\Gamma}\sigma}$ predicts.**

The corrected decay takes the form:

$$\rho_{\text{off}}(\sigma) \leq e^{-2\pi}\left(1 - \kappa\,\sigma^2 + \mathcal{O}(\sigma^3)\right)$$

where $\kappa$ is the scalar curvature of the Bures metric at the initial state. Since $\kappa \leq 0$ for the relevant directions, the correction term is **non-positive** — the bound gets tighter, not looser.

---

## 5. The Quantum Cramér–Rao Connection

The tighter bound also follows from the **quantum Cramér–Rao inequality**. For any parameter $\theta$ encoded in a quantum state $\rho(\theta)$:

$$\mathrm{Var}(\hat{\theta}) \geq \frac{1}{F_Q[\rho, \theta]}$$

where $F_Q$ is the quantum Fisher information (SLD metric). The classical Cramér–Rao bound uses the classical Fisher information $F_C$, and:

$$F_Q \geq F_C$$

with equality **only** for commuting observables. For the collapse process, the relevant observable is the which-branch operator $\Pi = |L\rangle\langle L| - |R\rangle\langle R|$ of the spatial superposition. This does **not** commute with the Hamiltonian generating the collapse, so $F_Q > F_C$ strictly.

The CramerRao.lean file in the QM library already establishes the classical Cramér–Rao bound and derives Heisenberg from it. Extending to the quantum (SLD) version gives a strictly tighter uncertainty bound, which translates directly to a strictly tighter decoherence rate:

$$\Gamma_{\text{Bures}} \geq \Gamma_{\text{Lindblad}}$$

The gap between them is controlled by the non-commutativity of the state, which is measured by the **Wigner-Yanase skew information** — another object from quantum information geometry.

---

## 6. The Dually Flat Structure of the Collapse

The key structural insight from Amari's theory: the space of quantum states carries a **dually flat structure** with respect to the $e$-connection ($\alpha = +1$) and the $m$-connection ($\alpha = -1$).

In this structure:

- The **$e$-coordinates** (exponential/natural parameters) are $\theta^i = $ components of $\log\rho$ (the modular Hamiltonian).
- The **$m$-coordinates** (mixture/expectation parameters) are $\eta_i = $ components of $\rho$ itself.
- The **Legendre transform** relates them: $\eta_i = \partial_i \psi(\theta)$, $\theta^i = \partial^i \varphi(\eta)$.
- The **canonical divergence** is the quantum relative entropy (Araki/Umegaki): $D[\rho\|\sigma] = \mathrm{Tr}[\rho(\log\rho - \log\sigma)]$.
- The **Hessian** of the divergence at the diagonal recovers the Fisher metric.

The decoherence process — moving from a coherent state $\rho$ to its decohered (diagonal) version $\rho_{\text{diag}}$ — is an **$m$-projection**: the nearest point to $\rho$ in the $m$-flat submanifold of diagonal states.

The **generalized Pythagorean theorem** then applies:

$$D[\rho_0 \,\|\, \rho_{\text{final}}] = D[\rho_0 \,\|\, \rho_{\text{proj}}] + D[\rho_{\text{proj}} \,\|\, \rho_{\text{final}}]$$

whenever the $e$-geodesic from $\rho_{\text{proj}}$ to $\rho_{\text{final}}$ is orthogonal to the $m$-flat submanifold at $\rho_{\text{proj}}$.

This decomposition is **exact** — not an approximation. The first term $D[\rho_0 \| \rho_{\text{proj}}]$ is the **quantum** (coherence) part of the entropy production. The second term $D[\rho_{\text{proj}} \| \rho_{\text{final}}]$ is the **thermal** part. These correspond precisely to the two entropy channels in the E-Process framework:

| Channel | Divergence component | E-Process name |
|---------|---------------------|----------------|
| Quantum (entanglement) | $D[\rho_0 \| \rho_{\text{proj}}]$ | $\Gamma_q = E_{\text{grav}}/\hbar$ |
| Thermal (environmental) | $D[\rho_{\text{proj}} \| \rho_{\text{final}}]$ | $\propto T$ |

The Pythagorean decomposition explains **why** the two channels are independent and **why** they add: it is a consequence of the orthogonality in the dually flat structure.

---

## 7. The Compton Regularization as Bures Curvature

The E-Process regularized collapse rate is:

$$\tilde{\Gamma}(\Delta s) = \frac{\lambda_C}{\Delta s}\left(1 - e^{-\Delta s^2/\lambda_C^2}\right)$$

where $\lambda_C = \hbar/(mc)$ is the Compton wavelength. This has three key properties:

1. $\tilde{\Gamma}(0) = 0$ (trace preservation)
2. $\tilde{\Gamma}(\Delta s) \to \lambda_C/\Delta s$ as $\Delta s \to \infty$ (Penrose limit)
3. $\tilde{\Gamma}(\Delta s) > 0$ for $\Delta s > 0$ (monotonic decoherence)

The conjecture from the information-geometric perspective: **this regularization is the Bures geodesic distance** on the two-state quantum manifold parameterized by the proper separation $\Delta s$.

The evidence:

- The Compton wavelength $\lambda_C$ sets the **curvature radius** of the quantum statistical manifold at the Planck scale. States separated by less than $\lambda_C$ are "close" on the Bures manifold — the curvature suppresses the collapse rate.
- The Gaussian factor $1 - e^{-\Delta s^2/\lambda_C^2}$ has exactly the form of a **curvature correction** to a geodesic distance: the deviation from linearity is Gaussian in $\Delta s/\lambda_C$, which is the natural dimensionless ratio for curvature effects.
- The regularized separation $\sqrt{\Delta s^2 + \lambda_C^2}$ already used in `gravitationalSelfEnergy` is the **Bures norm** of the tangent vector at the coherent state.

If this identification is correct, then:

- The Compton wavelength regularization is not an *ad hoc* UV cutoff. It is the **intrinsic curvature scale** of the quantum statistical manifold.
- The factor $1 - e^{-\Delta s^2/\lambda_C^2}$ is not chosen for convenience. It is the **exact geodesic correction** on the Bures manifold of a two-state system.
- The tighter bound follows automatically: the Bures geodesic gives a **smaller** coherence after one modular cycle than the flat Lindblad estimate.

---

## 8. The Computation

To obtain the explicit tighter bound, one needs to compute the **scalar curvature of the Bures metric** on the two-dimensional manifold parameterized by $(\Delta s, \Gamma)$.

For a two-level system with density matrix:

$$\rho = \begin{pmatrix} p & c \\ \bar{c} & 1-p \end{pmatrix}$$

the Bures metric is:

$$ds^2_B = \frac{dp^2}{4p(1-p)} + \frac{|dc|^2}{p(1-p)} \cdot \frac{1}{1 + 2\sqrt{p(1-p)} - 2|c|^2/(p(1-p))}$$

The scalar curvature of this metric, evaluated at the initial coherent state, gives $\kappa$. The corrected bound is then:

$$e^{-2\pi}(1 + |\kappa|\sigma_{\max}^2)^{-1}$$

which is **strictly smaller** than $e^{-2\pi}$ for $\kappa \neq 0$.

The dependence on $\Delta s/\lambda_C$ enters through the parameterization: the initial coherence $|c|$ is determined by the superposition structure, and the population $p$ is determined by the gravitational self-energy.

This is one explicit calculation — the Ricci scalar of a known 2D metric — and it would be **new**: no one has computed the Bures curvature correction to the Diósi-Penrose collapse rate.

---

## 9. What This Means for the Formalization

The formalization path is:

1. **Layer 0**: Define the conjugate connection manifold structure $(g, \nabla, \nabla^*)$ satisfying $X\langle Y, Z\rangle = \langle \nabla_X Y, Z\rangle + \langle Y, \nabla^*_X Z\rangle$. This is pure differential geometry.

2. **Layer 1**: Define the dually flat structure — both connections flat, dual coordinates $(\theta, \eta)$ related by Legendre transform, canonical divergence $D[p:q] = \psi(\theta) + \varphi(\eta') - \theta^i\eta'_i$.

3. **Recognition theorem**: Prove that the existing E-Process two-channel structure is an instance of the Pythagorean decomposition on a dually flat manifold.

4. **Bures curvature**: Compute $\kappa$ for the two-state system, as a function of $\Delta s/\lambda_C$.

5. **Tighter bound theorem**: Prove that $\rho_{\text{off}}(\text{after one modular cycle}) < e^{-2\pi}(1 + |\kappa|\cdot 4\pi^2)^{-1}\,\rho_0$, which is strictly less than $0.003\,\rho_0$.

Steps 1–3 connect the existing library to information geometry. Steps 4–5 produce a new physical result.

---

## 10. Broader Implications

The same curvature correction applies everywhere the $2\pi$ modular threshold appears in the Superior framework:

| Module | Current bound | IG-corrected bound |
|--------|---------------|-------------------|
| E-Process (decoherence) | $e^{-2\pi} < 0.003$ | $e^{-2\pi}(1+\|\kappa\|\sigma^2)^{-1}$ — tighter |
| Objective Reduction (measurement) | $\Delta S \geq 2\pi$ nats | Geodesic entropy $\geq 2\pi$ — fewer nats needed along the geodesic |
| Shape Dynamics (classical limit) | $f_q(T) = E_{\text{grav}}/(E_{\text{grav}} + k_BT)$ | Curvature-corrected interpolation — sharper crossover |
| Nanothermodynamics (subdivision) | Entropic cost of algebraic cut | Bures-geodesic cost — different scaling with subsystem size |

In every case, the curvature of the quantum statistical manifold makes the transition **sharper** — coherence is lost faster, measurement thresholds are reached sooner, and the quantum-to-classical crossover is steeper.

The flat-space estimates in the current library are **lower bounds** on the actual decoherence rates. Information geometry upgrades them to **geodesic estimates** that are tighter by a factor depending on the Bures scalar curvature.

---

## 11. Summary

| Question | Answer |
|----------|--------|
| Can IG tighten the 0.3% bound? | **Yes** — via Bures curvature corrections |
| Is the correction physically meaningful? | **Yes** — especially near the Compton scale where curvature is large |
| Is it computable? | **Yes** — one Ricci scalar calculation on a 2D metric |
| Has anyone done it? | **No** — this would be a new result |
| Does it fit the existing library? | **Yes** — as a recognition theorem + one new computation |
| Is the Compton regularization already the Bures geodesic? | **Conjectured** — verifiable by direct computation |

The punchline: the E-Process already contains information geometry in disguise. The Compton wavelength regularization, the two entropy channels, the Pythagorean-like independence of quantum and thermal decoherence — these are all shadows of the dually flat structure on the quantum statistical manifold.

Making the information geometry explicit does not change the physics. It **names** it correctly, connects it to a sixty-year mathematical tradition, and produces strictly tighter bounds as a consequence.

---

## References

- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
- S. Amari & H. Nagaoka, *Methods of Information Geometry*, AMS/Oxford, 2000.
- D. Petz, "Monotone metrics on matrix spaces," *Lin. Alg. Appl.* **244** (1996), 81–96.
- S.L. Braunstein & C.M. Caves, "Statistical distance and the geometry of quantum states," *Phys. Rev. Lett.* **72** (1994), 3439.
- A. Uhlmann, "The metric of Bures and the geometric phase," *Groups and Related Topics*, Kluwer, 1992.
- L. Diósi, "A universal master equation for the gravitational violation of quantum mechanics," *Phys. Lett. A* **120** (1987).
- R. Penrose, "On gravity's role in quantum state reduction," *Gen. Rel. Grav.* **28** (1996).