# Thermal Time's Generator Under Lorentz Transformation

For a Gibbs state ρ = e^{-βH}/Z, the modular operator is:

$$\Delta = e^{-\beta H}$$

The generator of modular flow is:

$$K = -\ln \Delta = \beta H$$

Under a Lorentz boost, energy transforms:

$$H \to H' = \gamma H$$

---

**Landsberg (β' = β, i.e., T' = T):**

$$K' = \beta' H' = \beta (\gamma H) = \gamma K$$

Therefore:

$$\Delta' = e^{-K'} = e^{-\gamma K} = \Delta^\gamma$$

The modular flow:

$$\sigma'_s(A) = \Delta'^{is} A \Delta'^{-is} = \Delta^{i\gamma s} A \Delta^{-i\gamma s} = \sigma_{\gamma s}(A)$$

**Thermal time rescales.** The parameter s → γs. Different observers disagree on how much thermal time has elapsed.

---

**Ott (β' = β/γ, i.e., T' = γT):**

$$K' = \beta' H' = \frac{\beta}{\gamma}(\gamma H) = \beta H = K$$

Therefore:

$$\Delta' = e^{-K'} = e^{-K} = \Delta$$

The modular flow:

$$\sigma'_s(A) = \Delta'^{is} A \Delta'^{-is} = \Delta^{is} A \Delta^{-is} = \sigma_s(A)$$

**Thermal time is invariant.** All observers agree on s.

---

**The KMS Condition**

A state ω satisfies the KMS condition at inverse temperature β if:

$$\omega(A \sigma_{i\beta}(B)) = \omega(BA)$$

for all A, B in the algebra.

Under Landsberg: β is invariant but σ_s → σ_{γs}, so the KMS condition becomes:

$$\omega(A \sigma_{i\gamma\beta}(B)) = \omega(BA)$$

The state satisfies KMS at effective inverse temperature γβ, not β. **Equilibrium is frame-dependent.**

Under Ott: both K and the flow are invariant. The KMS condition:

$$\omega(A \sigma_{i\beta}(B)) = \omega(BA)$$

is preserved exactly. **Equilibrium is frame-independent.**

---

**The Cocycle Radon-Nikodym Theorem**

For two faithful normal states ω and φ on a von Neumann algebra M, there exists a cocycle u_t such that:

$$\sigma^\phi_t = \text{Ad}(u_t) \circ \sigma^\omega_t$$

where u_t satisfies:

$$u_{s+t} = u_s \sigma^\omega_s(u_t)$$

This means the modular flows differ only by inner automorphisms. The projection to outer automorphisms is state-independent:

$$\delta: \mathbb{R} \to \text{Out}(M)$$

**This is the Connes invariant.** It classifies Type III factors.

Under Landsberg: K → γK means this canonical map becomes observer-dependent:

$$\delta_v: \mathbb{R} \to \text{Out}(M)$$

The *algebraic classification of the factor* would depend on velocity. Nonsense.

Under Ott: K is invariant, so δ is invariant. The algebraic structure is preserved.

---

**Proper Time vs. Thermal Time**

The relationship between thermal time s and proper time τ:

$$\frac{ds}{d\tau} = \frac{2\pi T}{\hbar}$$

Under Ott:
- T → γT
- But proper time dilates: dτ → dτ' = dτ/γ

So:

$$\frac{ds}{d\tau'} = \frac{2\pi \gamma T}{\hbar} = \gamma \cdot \frac{2\pi T}{\hbar}$$

But ds is invariant (same thermal time for all observers), and:

$$d\tau' = \frac{\hbar}{2\pi \gamma T} ds = \frac{1}{\gamma} \cdot \frac{\hbar}{2\pi T} ds = \frac{d\tau}{\gamma}$$

**Proper time dilates correctly.** Thermal time is universal.

---

**Entropy**

The von Neumann entropy:

$$S = -\text{Tr}(\rho \ln \rho) = \beta \langle H \rangle - \ln Z = \beta E - F/T$$

Under Ott:
- E → γE
- T → γT  
- β → β/γ
- F → γF (free energy is energy)

So:

$$S' = \beta' E' - F'/T' = \frac{\beta}{\gamma}(\gamma E) - \frac{\gamma F}{\gamma T} = \beta E - F/T = S$$

**Entropy is invariant.** (As it must be—it counts microstates.)

Under Landsberg:
- E → γE
- T → T
- β → β

$$S' = \beta E' - F'/T = \beta \gamma E - \gamma F/T = \gamma(\beta E - F/T) = \gamma S$$

**Entropy transforms.** Microstates become non-integers. Catastrophe.

---

**The Bisognano-Wichmann Theorem**

For the vacuum state |0⟩ restricted to the Rindler wedge algebra A_R, the modular flow IS the boost:

$$\sigma_s = \alpha_{2\pi s}^{\text{boost}}$$

The modular generator K is proportional to the boost generator K₁:

$$K = 2\pi K_1$$

The Unruh temperature emerges:

$$T_U = \frac{\hbar a}{2\pi c k_B}$$

Under Ott, this whole structure is Lorentz invariant. The vacuum restricted to ANY Rindler wedge (related by boosts) gives the same modular structure.

Under Landsberg, different Rindler wedges would have different modular parameters. The vacuum would not be Lorentz invariant.

---

**Summary: What Ott Preserves**

| Structure | Under Ott |
|-----------|-----------|
| Generator K = βH | Invariant |
| Modular operator Δ | Invariant |
| Modular flow σ_s | Invariant |
| KMS condition | Preserved |
| Connes invariant δ | Preserved |
| Entropy S | Invariant |
| Equilibrium | Frame-independent |
| Factor classification | Preserved |

**Landsberg breaks all of these.**

---