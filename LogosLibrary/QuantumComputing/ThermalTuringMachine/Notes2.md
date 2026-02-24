Now I see the full architecture. This is the real upgrade — you're not just fixing the axiom; you're *discharging* it.

The connection is:

```
ThermalTM.step (δ : Q → Γ → Option (Q × Γ × Direction))
       │
       │  induces pushforward on distributions over Config Q Γ
       ▼
StatisticalManifold (distribution over configs at each step)
       │
       │  Fisher inner product: ⟨v,w⟩_θ = E_θ[s_v · s_w]
       │  Fisher norm: ‖v‖_θ = √(g_θ(v,v))
       ▼
Fisher–Rao displacement per step
       │
       │  Cramér–Rao: variance ≥ 1/I(θ)
       │  Locality of δ: O(1) cells affected ⟹ O(1) Fisher displacement
       ▼
TMTransition.displacement_bounded  ← Axiom 5 DISCHARGED
       │
       │  and simultaneously:
       │  dissipation ≥ kT ln 2 (Landauer)
       │  entropy production = β · dissipation ≥ ln 2
       │  Fisher–Rao displacement ≤ f(entropy production)
       ▼
Thermodynamic length = ∑ d_FR(p_t, p_{t+1}) ≤ T · Δ
```

The Cramér–Rao inequality is doing double duty: in the quantum uncertainty stack it gives you Heisenberg (σ_A σ_B ≥ ℏ/2), and here it bounds the per-step Fisher displacement from the entropy production per step. The *same inequality* limiting measurement precision also limits computational speed. The sibling theorems aren't just an analogy — they literally share a lemma.

And the Landauer compliance on the ThermalTM gives you the thermodynamic floor: each irreversible step produces ≥ ln 2 nats of entropy, which through `stepEntropyProduction = β · stepDissipation` connects to the Fisher–Rao displacement. The KMS grounding means this isn't a postulate — the temperature is real equilibrium temperature from the modular automorphism group.

Ready to build the bridge. What do you have so far, or are we writing it from scratch?