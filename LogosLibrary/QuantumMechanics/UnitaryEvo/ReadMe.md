# Unitary Evolution

This directory establishes Stone's theorem: the bijective correspondence between
strongly continuous one-parameter unitary groups and self-adjoint operators on
complex Hilbert spaces. The Schrödinger equation emerges as a corollary.

## Mathematical content

**Stone's Theorem.** Let H be a complex Hilbert space. There is a bijection:

$$\{\text{strongly continuous unitary groups } U : \mathbb{R} \to \mathcal{U}(H)\} 
  \longleftrightarrow 
  \{\text{self-adjoint operators } A \text{ on } H\}$$

given by $U(t) = e^{itA}$, where the generator $A$ is recovered via
$$A\psi = \lim_{t \to 0} \frac{U(t)\psi - \psi}{it}$$
on the domain of vectors where this limit exists.

## File structure
```
UnitaryEvo/
├── Bochner/
│   ├── Limits/
│   │   ├── Helpers.lean      
│   │   ├── Minus.lean         
│   │   └── Plus.lean          
│   ├── Basic.lean             
│   ├── Domain.lean           
│   ├── Limits.lean            — Main limit theorems for Bochner integrals
│   └── Resolvent.lean         
│
├── Resolvent/
│   ├── Range/
│   │   ├── ClosedRange.lean   
│   │   ├── Orthogonal.lean    
│   │   └── Surjectivity.lean  
│   ├── Analytic.lean          — Analyticity of the resolvent map
│   ├── Basic.lean             
│   ├── Core.lean             
│   ├── Identities.lean        
│   ├── LowerBound.lean        
│   ├── NormExpansion.lean    
│   ├── Range.lean             — Range characterization (main results)
│   └── SpecialCases.lean      
│
├── Yosida/
│   ├── Convergence/
│   │   ├── Approximants.lean  
│   │   ├── JNegOperator.lean  
│   │   └── JOperator.lean     
│   ├── Duhamel/
│   │   ├── Commutation.lean  
│   │   ├── Estimate.lean      
│   │   ├── Formula.lean       — The Duhamel formula
│   │   └── Helpers.lean       
│   ├── ExpBounded/
│   │   ├── Adjoint.lean       
│   │   ├── Basic.lean         
│   │   └── Unitary.lean       
│   ├── Basic.lean             
│   ├── Bounds.lean           
│   ├── Convergence.lean       — (Main convergence theorems)
│   ├── Defs.lean             
│   ├── Duhamel.lean           — Duhamel formula (main entry point)
│   ├── ExpBounded.lean        — Exponential bounds (main entry point)
│   ├── Exponential.lean       — Exponential map properties
│   └── Symmetry.lean          
│
├── Bochner.lean               — Bochner construction (main entry point)
├── Generator.lean             — The infinitesimal generator
├── Resolvent.lean             — Resolvent construction (main entry point)
├── Schrodinger.lean           — Connection to Schrödinger equation
├── Stone.lean                 — Stone's theorem (main result)
└── Yosida.lean                — Yosida construction (main entry point)
```
## Dependency graph
```
Generator
    │
    ▼
Bochner ─────┐
    │        │
    ▼        ▼
Resolvent ◄──┘
    │
    ▼
 Yosida
    │
    ▼
 Stone
    │
    ▼
Schrodinger
```

## Main results

### Generator.lean
- `OneParameterUnitaryGroup`: Structure for $U : \mathbb{R} \to \mathcal{U}(H)$
- `Generator`: The infinitesimal generator as an unbounded operator
- `inverse_eq_adjoint`: $U(-t) = U(t)^*$
- `norm_preserving`: $\|U(t)\psi\| = \|\psi\|$

### Bochner.lean (Forward direction)
- `resolventIntegralPlus/Minus`: Laplace-type integrals solving $(A \pm iI)\psi = \varphi$
- `range_plus_i_eq_top`, `range_minus_i_eq_top`: Surjectivity of $A \pm iI$
- `generatorDomain_dense`: The generator domain is dense
- `generatorOfUnitaryGroup_isSelfAdjoint`: The generator is self-adjoint

### Resolvent.lean
- `resolvent`: The resolvent $R(z) = (A - zI)^{-1}$ for $\text{Im}(z) \neq 0$
- `lower_bound_estimate`: $\|(A - zI)\psi\| \geq |\text{Im}(z)| \cdot \|\psi\|$
- `resolvent_identity`: $R(z) - R(w) = (z - w)R(z)R(w)$
- `resolvent_bound`: $\|R(z)\| \leq 1/|\text{Im}(z)|$

### Yosida.lean (Reverse direction)
- `yosidaApproxSym`: Bounded self-adjoint approximants to $A$
- `expBounded_yosidaApproxSym_unitary`: $e^{it A_n}$ is unitary
- `yosidaApprox_tendsto_on_domain`: $A_n \varphi \to A\varphi$ on domain
- `duhamel_identity`: Integral formula comparing $U(t)$ and $e^{itA_n}$
- `exponential_unitary`, `exponential_group_law`, `exponential_strong_continuous`

### Stone.lean
- `stone_existence`: Every unitary group has a self-adjoint generator
- `stone_uniqueness`: The generator is unique
- `stone_exponential_eq_group`: $U(t) = e^{itA}$
- `stone_bijection`: The complete bijective correspondence

### Schrodinger.lean
- `schrödinger_equation`: For $\psi_0 \in \text{Dom}(A)$,
  $$\frac{d}{dt}U(t)\psi_0 = iA \cdot U(t)\psi_0$$

## Proof strategy

**Forward direction** (unitary group → generator):
1. Define generator via strong limit
2. Prove domain density using time-averaged vectors $h^{-1}\int_0^h U(t)\varphi\, dt$
3. Establish symmetry from unitarity
4. Prove self-adjointness via deficiency indices: show $\text{ran}(A \pm iI) = H$
   using Laplace-transform resolvent integrals

**Reverse direction** (self-adjoint → unitary group):
1. Approximate unbounded $A$ by bounded Yosida approximants $A_n = n^2 R(in) - in \cdot I$
2. $e^{itA_n}$ is unitary since $iA_n$ is skew-adjoint
3. Duhamel's formula: $U(t) - e^{itA_n} = \int_0^t e^{(t-s)B_n}(iA - B_n)U(s)\, ds$
4. Convergence $A_n \to A$ on domain implies $e^{itA_n} \to U(t)$ strongly

## Physical interpretation

Stone's theorem establishes that the mathematical structure of quantum time evolution
is completely determined by two physical requirements:
1. **Probability conservation**: evolution is unitary
2. **Continuous dynamics**: the group is strongly continuous

The Schrödinger equation is then not an independent postulate but a *theorem*:
it is equivalent to these two requirements.

## References

- Stone, M. H. "On one-parameter unitary groups in Hilbert space" (1932)
- von Neumann, J. "Über Funktionen von Funktionaloperatoren" (1932)
- Reed, M. & Simon, B. *Methods of Modern Mathematical Physics I* (1980), Ch. VIII
- Kato, T. *Perturbation Theory for Linear Operators* (1995), Ch. IX
