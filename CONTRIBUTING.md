# Contributing to Logos Library

**Current Phase**: Private development with quality control

---

## The Standard

Every line of code in this library is **formally verified**. No exceptions.

If Lean 4's type checker doesn't verify it, it doesn't go in.

---

## What We Accept

### ✅ Accepted Contributions

1. **New Theorems**: Complete formal proofs with blueprints
2. **Course Material**: Pedagogical content with verified examples
3. **Detector Logic**: Validators grounded in physical constraints
4. **Bug Fixes**: Maintaining proof validity
5. **Documentation**: Improving clarity without sacrificing rigor

### ❌ Not Accepted

- Informal proofs or "proof sketches"
- Code with `sorry` outside of designated WIP sections
- Dependencies that break our pinned versions
- Anything violating our yardsticks (Thermodynamics, GR, Lean 4, QM)

---

## Development Workflow

### For New Features

```bash
# Create a feature branch
git checkout -b feature/stone-resolvent-lemma

# Make changes
# ... edit files ...

# Verify locally
lake build

# Commit with descriptive message
git add .
git commit -m "[DeepTheorems] Stone: Prove resolvent identity lemma"

# Push to remote
git push origin feature/stone-resolvent-lemma

# Open PR on GitHub (for review on major changes)
```

### For Quick Fixes

```bash
# Small changes can go directly to main after CI passes
git checkout main
git pull
# ... make small fix ...
lake build  # Verify
git commit -m "[Units] Physics: Fix Planck constant dimension"
git push origin main
```

---

## Branch Strategy

- **`main`**: Protected. All code must compile. CI must pass.
- **`feature/*`**: Feature branches for major work
- **`wip/*`**: Work-in-progress branches (can have `sorry`)

### Main Branch Protection

- Requires CI to pass (Lean verification)
- PR review recommended for:
  - New sections or major architecture changes
  - Completed theorem proofs (for "official" verification)
  - API-breaking changes

- Direct push acceptable for:
  - Incremental proof progress
  - Documentation updates
  - Bug fixes
  - Routine cleanup

---

## Commit Message Convention

Use descriptive commit messages with section tags:

```
[Section] Component: Description

Examples:
✅ [DeepTheorems] Stone: Add generator structure definitions
✅ [DeepTheorems] Robertson: Complete uncertainty principle proof
✅ [Units] Physics/Quantum: Add Planck constant with proper dimensions
✅ [Classes] QM/Lecture5: Complete entanglement formalization
✅ [Detectors] Battery: Fix thermodynamic constraint check
✅ [Docs] Architecture: Update roadmap section
```

---

## Blueprint Convention

Every major theorem in `DeepTheorems/` should have a blueprint. See [DeepTheorems/README.md](DeepTheorems/README.md) for the template.

**Required sections**:
- Mathematical statement
- Proof strategy (with difficulty estimates)
- Implementation notes
- Current progress checklist

**Example**: `DeepTheorems/Quantum/Evolution/Stone/Blueprint.md`

---

## Code Standards

### Type Safety
```lean
-- ✅ DO: Use typed units
def planck_constant : Energy * Time := ⟨6.62607015e-34, by units⟩

-- ❌ DON'T: Use raw floats
def planck_constant : Float := 6.62607015e-34
```

### Domain Tracking
```lean
-- ✅ DO: Track operator domains explicitly (Robertson pattern)
structure UnboundedOperator where
  op : H →ₗ[ℂ] H
  domain : Submodule ℂ H
  dense_domain : Dense (domain : Set H)

-- ❌ DON'T: Assume operators work everywhere
def operator : H → H := ...
```

### Documentation
```lean
-- ✅ DO: Explain WHY in comments
/-- 
Resolvent identity: R(z) - R(w) = (w - z)R(z)R(w)

This is the KEY to proving spectral theorem. The identity shows
resolvents at different points are related by simple composition.
-/
theorem resolvent_identity ...

-- ❌ DON'T: Just state WHAT
/-- Resolvent identity -/
theorem resolvent_identity ...
```

---

## Testing Your Changes

```bash
# Verify everything compiles
lake build

# Test specific section
lake build DeepTheorems.Quantum.Evolution.Stone

# Run test suite
lake test

# Check for sorry
grep -r "sorry" --include="*.lean" DeepTheorems/
```

Before pushing to main, ensure:
- [ ] Code compiles (`lake build`)
- [ ] Tests pass (`lake test`)
- [ ] No new `sorry` outside WIP sections
- [ ] Documentation updated if needed

---

## Dependencies

**DO NOT UPDATE** mathlib or other dependencies without coordination:

```bash
# ❌ DON'T run this without discussing first
lake update

# ✅ DO stay on pinned versions
# (lake-manifest.json locks everything)
```

**Why**: Mathlib API changes can break proofs. We update at strategic milestones, not mid-theorem.

---

## Getting Help

- **Stuck on a proof?** Open a discussion issue
- **Lean error unclear?** Ask in the issue or check Lean Zulip
- **Unsure about approach?** Review similar proofs (e.g., Robertson for operator theory)

---

## Review Process

### What Reviewers Check

1. **Correctness**: Does it compile and prove what it claims?
2. **Style**: Follows our conventions?
3. **Documentation**: Blueprint or comments adequate?
4. **Dependencies**: No `sorry` leakage?
5. **Tests**: Appropriate test coverage?

### Review Turnaround

- Simple fixes: Same day
- New lemmas: 1-2 days
- Major theorems: 1 week (needs careful verification)

---

## Quality Over Speed

We'd rather have 100 lines of perfect proof than 10,000 lines of "probably works."

Take your time. Get it right. Lean will tell you when you're done.

---

## Questions?

Open an issue or discuss in team channels.

**Remember**: If you're unsure, ask. Breaking proofs is expensive to fix.
