# Deep Theorems: Blueprint Convention

This directory contains graduate-level formal verification of major physics theorems.

---

## Blueprint Standard

Every major theorem should have an associated `Blueprint.md` file following this template:

```markdown
# [THEOREM NAME] Blueprint

## Status
**Current**: [IN PROGRESS / COMPLETE / PLANNED]  
**Lines**: ~[estimate]  
**Started**: [date]  
**Target Completion**: [date]

## Dependencies
- Mathlib: [specific modules needed]
- LogosLibrary: [internal dependencies]
- External: [any other requirements]

## Mathematical Statement

[Precise statement of what's being proven - LaTeX or Lean syntax]

## Proof Strategy

[High-level approach with numbered steps]

### Step 1: [Name]
- **Goal**: [what we're proving]
- **Method**: [technique/approach]
- **Difficulty**: [Easy / Medium / Hard / Very Hard]
- **Status**: [Not Started / In Progress / Complete]
- **Dependencies**: [prerequisite lemmas]
- **Estimated Lines**: ~[number]

### Step 2: [Name]
[repeat structure]

## Implementation Notes

[Technical considerations, tricks, patterns to use]

**Example**:
- Use Robertson's domain-tracking pattern for unbounded operators
- Need Bochner integration for vector-valued functions
- Spectral theorem requires careful treatment of measure theory

## Current Progress

- [ ] Structure definitions
- [ ] Key lemmas stated
- [ ] Lemma 1 proven
- [ ] Lemma 2 proven
- [ ] Main theorem assembled
- [ ] Examples computed
- [ ] Tests written

## Compilation Status

**Last successful build**: [date]  
**Known issues**: [list any sorries or problems]

## Future Work

[What comes after this theorem, how it connects to other work]

## References

- [Paper 1]
- [Textbook, Ch. X]
- [Other relevant sources]
```

---

## Example: Stone's Theorem

See `Quantum/Evolution/Stone/Blueprint.md` for a complete example following this template.

Key features of a good blueprint:
- **Honest about difficulty**: Mark hard parts as hard
- **Explicit dependencies**: What you need before you can proceed
- **Progress tracking**: Clear checklist of what's done
- **Implementation notes**: Technical tricks and patterns

---

## File Organization

```
DeepTheorems/
├── Quantum/
│   ├── Uncertainty/
│   │   └── Robertson/
│   │       ├── Blueprint.md         ✅ COMPLETE
│   │       ├── Core.lean            ✅ PROVEN
│   │       ├── Examples.lean        ✅ COMPLETE
│   │       └── Tests.lean           ✅ COMPLETE
│   └── Evolution/
│       └── Stone/
│           ├── Blueprint.md         ✅ COMPLETE
│           ├── Core.lean            🔄 IN PROGRESS
│           ├── Resolvent.lean       🔄 IN PROGRESS
│           └── Spectral.lean        ⏳ PLANNED
├── Gravity/
│   └── Thermodynamics/
│       ├── Blueprint.md             🔄 DRAFT
│       └── Padmanabhan.lean         ⏳ PLANNED
└── Holography/
    └── RyuTakayanagi/
        ├── Blueprint.md             ⏳ PLANNED
        └── Core.lean                ⏳ PLANNED
```

---

## Status Indicators

- ✅ **COMPLETE**: Fully proven, no sorries, tests passing
- 🔄 **IN PROGRESS**: Active work, may have sorries
- ⏳ **PLANNED**: Blueprint exists, not started
- 🚧 **BLOCKED**: Waiting on dependencies

---

## Proof Patterns

### Robertson Pattern (Unbounded Operators)

Use this for any quantum operator with domain issues:

```lean
structure UnboundedObservable where
  op : H →ₗ[ℂ] H
  domain : Submodule ℂ H
  dense_domain : Dense (domain : Set H)
  symmetric : ∀ ψ φ ∈ domain, ⟪op ψ, φ⟫ = ⟪ψ, op φ⟫
```

**When to use**: Position, momentum, Hamiltonian, any unbounded operator

**Proven to work**: Robertson's uncertainty principle ✅

### Stone Pattern (Generator + Evolution)

For time evolution problems:

```lean
structure Generator (U : OneParameterUnitaryGroup H) where
  op : H →ₗ[ℂ] H
  domain : Submodule ℂ H
  generator_formula : ...
  domain_invariant : ...
```

**When to use**: Quantum dynamics, time evolution

**Status**: In progress 🔄

---

## Quality Standards

Before marking a theorem COMPLETE:

- [ ] All `sorry` removed
- [ ] Tests written and passing
- [ ] Examples computed
- [ ] Documentation complete
- [ ] Blueprint updated with final status
- [ ] Code reviewed by team

---

## Contributing New Theorems

1. Create directory structure
2. Write blueprint FIRST (plan before coding)
3. Get blueprint reviewed
4. Implement in phases (structure → lemmas → main theorem)
5. Update blueprint as you learn
6. Mark complete when all criteria met

---

*For questions about blueprint conventions, open an issue or check existing blueprints for examples.*
