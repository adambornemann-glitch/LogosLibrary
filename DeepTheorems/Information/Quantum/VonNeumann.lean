/-
Author: Adam Bornemann
Created: 11/20/2025
Updated: 11/26/2025

=============================================================================================================
VON NEUMANN ENTROPY: QUANTUM INFORMATION THEORY
=============================================================================================================

This file develops the von Neumann entropy for quantum density operators,
the fundamental measure of quantum information and uncertainty.

PHYSICAL MOTIVATION:
  The von Neumann entropy S(ρ) = -Tr(ρ ln ρ) quantifies:
    - Quantum uncertainty: How much we don't know about a system
    - Entanglement: For bipartite pure states, S(ρ_A) measures entanglement
    - Information capacity: Bounds on quantum channel capacities
    - Thermodynamic entropy: Connection to statistical mechanics

HISTORICAL DEVELOPMENT:
  von Neumann (1927): Introduced density matrix formalism
  Shannon (1948): Information theory, classical entropy
  Wehrl (1978): Proved key properties of quantum entropy
  Holevo (1973): Information bounds in quantum systems
  Ryu-Takayanagi (2006): Connected to geometry via AdS/CFT

CONNECTION TO OTHER WORK:
  - Feeds into: Ryu-Takayanagi formula (Holography/EntanglementEntropy/)
  - Feeds into: Bekenstein bound (HolographicPrinciple.lean)
  - Requires: Density operators, partial trace, tensor products
  - Connects to: Quantum channels, quantum error correction

MATHEMATICAL CONTENT:
  §1 Definition via eigenvalues
  §2 Basic bounds (S ≥ 0, S ≤ ln n)
  §3 Pure state characterization (S = 0 ↔ pure)
  §4 Maximally mixed state (S = ln n)
  §5 Concavity S(pρ₁ + (1-p)ρ₂) ≥ p·S(ρ₁) + (1-p)·S(ρ₂)
  §6 Subadditivity (BLOCKED - needs tensor products)

CONVENTIONS:
  - 0 ln 0 = 0 by continuity (lim x→0⁺ x ln x = 0)
  - Natural logarithm (ln) used throughout
  - S denotes von Neumann entropy
  - n denotes dimension of Hilbert space

Built on:
  - QHilbert (Hilbert.lean) - trace, outer products
  - Quantum.State (state.lean) - density operators, eigenvalues

References:
  [1] von Neumann, "Mathematical Foundations of QM" (1932) - original definition
  [2] Nielsen & Chuang, "Quantum Computation and Quantum Information" Ch. 11
  [3] Wilde, "Quantum Information Theory" (2013) Ch. 11
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LogosLibrary.DeepTheorems.Core.State

namespace QInformation

open QState
open DensityOp
open QHilbert (QuantumState)
open Real (log)

notation "ℂ^" n => EuclideanSpace ℂ (Fin n)
/-!
=============================================================================================================
## Section 1: Von Neumann Entropy Definition
=============================================================================================================

The von Neumann entropy is defined as:

  S(ρ) = -Tr(ρ ln ρ) = -Σᵢ λᵢ ln λᵢ

where λᵢ are the eigenvalues of ρ.

The function η(x) = -x ln x is the "entropy function":
  - η(0) = 0 (by convention/continuity)
  - η(x) > 0 for 0 < x < 1
  - η(1) = 0
  - Maximum at x = 1/e with η(1/e) = 1/e

We use Real.log (natural logarithm) from Mathlib.
-/

/-- The entropy function η(x) = -x ln x.

This is the building block of von Neumann entropy. We adopt the convention
η(0) = 0, justified by the limit lim_{x→0⁺} x ln x = 0.

Properties:
  - η(0) = 0 (by definition)
  - η(x) > 0 for 0 < x < 1
  - η(1) = 0
  - Concave on [0, 1]
-/
noncomputable def eta (x : ℝ) : ℝ :=
  if x = 0 then 0 else -x * log x

/-- η(0) = 0 by convention. -/
@[simp]
theorem eta_zero : eta 0 = 0 := by simp [eta]

/-- η(1) = 0 since ln(1) = 0. -/
@[simp]
theorem eta_one : eta 1 = 0 := by simp [eta]

/-- The von Neumann entropy of a density operator.

Defined as S(ρ) = Σᵢ η(λᵢ) = -Σᵢ λᵢ ln λᵢ where λᵢ are eigenvalues.

This is the quantum generalization of Shannon entropy and measures
the quantum uncertainty or mixedness of the state.

Range: 0 ≤ S(ρ) ≤ ln n
  - S(ρ) = 0 iff ρ is pure
  - S(ρ) = ln n iff ρ is maximally mixed
-/
noncomputable def vonNeumannEntropy {n : ℕ} (ρ : DensityOp n) : ℝ :=
  ∑ i : Fin n, eta (ρ.eigenvalues i)

notation "S(" ρ ")" => vonNeumannEntropy ρ
/-!
=============================================================================================================
## Section 2: Basic Bounds
=============================================================================================================

The von Neumann entropy satisfies fundamental bounds:

  0 ≤ S(ρ) ≤ ln n

The lower bound follows from η(x) ≥ 0 for x ∈ [0, 1].
The upper bound follows from the maximum entropy principle:
entropy is maximized by the uniform distribution.

These bounds are tight:
  - S(ρ) = 0 for pure states (one eigenvalue = 1, rest = 0)
  - S(ρ) = ln n for maximally mixed state (all eigenvalues = 1/n)
-/

/-- The entropy function is non-negative on the probability simplex.

For all x ∈ [0, 1]:
  η(x) = -x ln x ≥ 0

**Case analysis:**

- x = 0: η(0) = 0 by convention (justified by continuity)

- 0 < x < 1: Both factors in -x · ln x are positive:
    - x > 0 (given)
    - -ln x > 0 (since ln x < 0 for x < 1)
  Thus η(x) > 0 strictly.

- x = 1: η(1) = -1 · ln 1 = -1 · 0 = 0

**Why this matters:**

Non-negativity of η is inherited by von Neumann entropy:

  S(ρ) = Σᵢ η(λᵢ) ≥ 0

since each eigenvalue λᵢ ∈ [0, 1] and each η(λᵢ) ≥ 0. This is the
fundamental lower bound on entropy — uncertainty is never negative.

**The shape of η:**

On [0, 1], the function η is:
  - Zero at both endpoints
  - Strictly positive on (0, 1)
  - Concave (∩-shaped)
  - Maximum at x = 1/e with η(1/e) = 1/e ≈ 0.368

This shape ensures that any genuine probability (neither 0 nor 1)
contributes positive entropy — uncertainty exists whenever an outcome
is neither certain nor impossible.

**Information-theoretic intuition:**

η(p) measures the "surprise" or "information content" of an event with
probability p, weighted by how often it occurs. Rare events (small p)
are surprising but infrequent; common events (large p) are frequent but
unsurprising. The weighting p · (-ln p) balances these effects, and
non-negativity says information is never destroyed by averaging.
-/
theorem eta_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : 0 ≤ eta x := by
  unfold eta
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte]
    have hxpos : 0 < x := lt_of_le_of_ne hx₀ (Ne.symm hx)
    have hlog : log x ≤ 0 := Real.log_nonpos hx₀ hx₁
    have h : 0 ≤ -log x := neg_nonneg.mpr hlog
    calc -x * log x = x * (-log x) := by ring
      _ ≥ 0 := mul_nonneg (le_of_lt hxpos) h




/-- Von Neumann entropy is non-negative for all quantum states.

For any density operator ρ:
  S(ρ) ≥ 0

**Proof:**

The entropy S(ρ) = Σᵢ η(λᵢ) is a finite sum over eigenvalues. Each term
satisfies η(λᵢ) ≥ 0 because:
  1. Eigenvalues of density operators satisfy λᵢ ∈ [0, 1]
     (from positivity and trace normalization)
  2. The entropy function η is non-negative on [0, 1]
     (from `eta_nonneg`)

A sum of non-negative terms is non-negative.

**Physical meaning:**

Entropy measures uncertainty, and uncertainty cannot be negative.
This is not merely convention — it reflects that:
  - We cannot know "more than everything" about a system
  - Pure states (complete knowledge) saturate the bound at S = 0
  - Any ignorance pushes S strictly positive

**Comparison with classical entropy:**

Shannon entropy H(X) = -Σᵢ pᵢ ln pᵢ satisfies H ≥ 0 for the same reason.
Von Neumann entropy generalizes this: the eigenvalues of ρ play the role
of a probability distribution, and the proof is identical.

**The complete picture:**

Combined with the upper bound S(ρ) ≤ ln n, we have:

  0 ≤ S(ρ) ≤ ln n

with both bounds tight:
  - S = 0 iff ρ is pure (minimum uncertainty)
  - S = ln n iff ρ = I/n (maximum uncertainty)

This interval [0, ln n] is the full range of possible quantum uncertainty
for an n-dimensional system.
-/
theorem entropy_nonneg {n : ℕ} (ρ : DensityOp n) : 0 ≤ S(ρ) := by
  unfold vonNeumannEntropy
  apply Finset.sum_nonneg
  intro i _
  exact eta_nonneg (eigenvalues_nonneg ρ i) (eigenvalues_le_one ρ i)

/-- The entropy function at the uniform distribution point.

For n ≥ 1:
  η(1/n) = (1/n) · ln(n)

**Derivation:**

  η(1/n) = -(1/n) · ln(1/n)
         = -(1/n) · (ln 1 - ln n)
         = -(1/n) · (-ln n)
         = (1/n) · ln n

**Role in maximum entropy:**

This identity is the key step in computing S(I/n) = ln n. The maximally
mixed state has all n eigenvalues equal to 1/n, so:

  S(I/n) = Σᵢ η(1/n) = n · η(1/n) = n · (1/n · ln n) = ln n

**Behavior in n:**

  - n = 1: η(1/1) = η(1) = 0 (trivial system, no uncertainty)
  - n = 2: η(1/2) = (1/2) ln 2 ≈ 0.347 (one bit per outcome)
  - n → ∞: η(1/n) → 0, but n · η(1/n) = ln n → ∞

The individual contribution η(1/n) shrinks, but the number of terms
grows, yielding total entropy ln n — the logarithm of the number of
distinguishable states.

**Connection to Boltzmann:**

In statistical mechanics, S = k_B ln Ω where Ω is the number of
microstates. The maximally mixed state treats all n basis states as
equally likely "microstates," recovering S = ln n (in natural units
where k_B = 1). This is the quantum Boltzmann entropy for a maximally
uncertain n-level system.
-/
theorem eta_inv (n : ℕ) (hn : 0 < n) :
    eta (1 / n) = (1 / n) * log n := by
  unfold eta
  have h1n : (1 : ℝ) / n ≠ 0 := by
    apply div_ne_zero
    · exact one_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  simp only [h1n, ↓reduceIte]
  rw [Real.log_div one_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn))]
  rw [Real.log_one]
  ring

/-- Von Neumann entropy is bounded above by ln n: S(ρ) ≤ ln n.

This is the maximum entropy principle: among all probability distributions
on n outcomes, entropy is maximized by the uniform distribution.

The proof uses the log-sum inequality / Gibbs' inequality:
  Σᵢ pᵢ ln(pᵢ/qᵢ) ≥ 0 for probability distributions p, q
with equality iff p = q.

Taking q = uniform gives: -Σᵢ pᵢ ln pᵢ ≤ ln n.

AXIOMATIZED: Requires concavity of log or Gibbs' inequality.
-/
axiom entropy_le_log_dim (n : ℕ) (hn : 0 < n) (ρ : DensityOp n) :
    S(ρ) ≤ log n

/-!
=============================================================================================================
## Section 3: Pure State Characterization
=============================================================================================================

A fundamental result: von Neumann entropy vanishes iff the state is pure.

  S(ρ) = 0 ↔ ρ is pure

Forward direction (pure → S = 0):
  Pure states have eigenvalues (1, 0, ..., 0).
  η(1) = 0 and η(0) = 0, so S = 0.

Reverse direction (S = 0 → pure):
  If S = 0 and each η(λᵢ) ≥ 0, then each η(λᵢ) = 0.
  On [0, 1], η(x) = 0 iff x = 0 or x = 1.
  Combined with Σᵢ λᵢ = 1, exactly one eigenvalue is 1.
  This means purity = Σᵢ λᵢ² = 1, so ρ is pure.
-/


/-- The entropy function η(x) = -x ln x vanishes exactly at the boundary of [0,1].

For x ∈ [0, 1]:
  η(x) = 0  ↔  x = 0 ∨ x = 1

**Analysis of η(x) = -x ln x:**

The function η : [0,1] → ℝ has the shape:
  - η(0) = 0 (by convention, justified by lim_{x→0⁺} x ln x = 0)
  - η increases on (0, 1/e), reaching maximum η(1/e) = 1/e
  - η decreases on (1/e, 1)
  - η(1) = 0 (since ln 1 = 0)

Thus η(x) > 0 strictly on the open interval (0, 1), vanishing only at endpoints.

**Why this matters for entropy:**

The zeros of η characterize certainty in probability:
  - x = 1: Event certain to occur (probability 1, no surprise)
  - x = 0: Event certain not to occur (probability 0, excluded)
  - 0 < x < 1: Genuine uncertainty, positive contribution to entropy

For von Neumann entropy S(ρ) = Σᵢ η(λᵢ), zero entropy requires every
η(λᵢ) = 0, forcing each eigenvalue to be 0 or 1 — the signature of
a pure state.

**Proof structure:**

(→) η(x) = 0 with x ≠ 0 implies -x ln x = 0. Since x ≠ 0, we have ln x = 0,
    so x = 1.

(←) Direct calculation: η(0) = 0 by definition, η(1) = -1·ln(1) = 0.
-/
theorem eta_eq_zero_iff {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    eta x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · -- eta x = 0 → x = 0 ∨ x = 1
    intro h
    unfold eta at h
    by_cases hx : x = 0
    · left; exact hx
    · simp only [hx, ↓reduceIte] at h
      -- h : -x * log x = 0
      have hxpos : 0 < x := lt_of_le_of_ne hx₀ (Ne.symm hx)
      have hne : x ≠ 0 := ne_of_gt hxpos
      have hmul : x * log x = 0 := by linarith
      rcases mul_eq_zero.mp hmul with hx' | hlog
      · exact absurd hx' hne
      · right
        exact Real.log_eq_zero.mp hlog |>.resolve_left hne |>.resolve_right (by linarith)
  · -- x = 0 ∨ x = 1 → eta x = 0
    intro h
    rcases h with rfl | rfl
    · exact eta_zero
    · exact eta_one



/-- Delta-distributed eigenvalues yield zero entropy.

If ρ has eigenvalues (1, 0, ..., 0) — that is, λᵢ₀ = 1 for some i₀ and
λᵢ = 0 for all i ≠ i₀ — then S(ρ) = 0.

**Direct calculation:**

  S(ρ) = Σᵢ η(λᵢ)
       = η(1) + Σ_{i ≠ i₀} η(0)
       = 0 + 0 + ... + 0
       = 0

**Role in the theory:**

This is the computational core of `entropy_pure` and the (←) direction
of `entropy_zero_iff_pure`. It reduces the entropy calculation for pure
states to the trivial facts η(0) = 0 and η(1) = 0.

The converse — showing that S(ρ) = 0 forces this eigenvalue structure —
is harder and requires the characterization `eta_eq_zero_iff` plus
the probability constraint Σᵢ λᵢ = 1.

**Physical meaning:**

A single eigenvalue of 1 means the density operator is a rank-1 projector
ρ = |ψ⟩⟨ψ|. The system is in a definite state |ψ⟩ with certainty —
no statistical mixture, no missing information, hence zero entropy.
-/
theorem entropy_of_pure_eigenvalues {n : ℕ} (ρ : DensityOp n) (_ /-hn-/ : 0 < n)
    (i₀ : Fin n) (hi₀ : ρ.eigenvalues i₀ = 1)
    (hrest : ∀ i, i ≠ i₀ → ρ.eigenvalues i = 0) :
    S(ρ) = 0 := by
  unfold vonNeumannEntropy
  have h : ∀ i : Fin n, eta (ρ.eigenvalues i) = 0 := by
    intro i
    by_cases hi : i = i₀
    · rw [hi, hi₀, eta_one]
    · rw [hrest i hi, eta_zero]
  simp only [h, Finset.sum_const_zero]



/-- Pure quantum states carry zero von Neumann entropy.

For any normalized state vector |ψ⟩, the corresponding density operator
ρ = |ψ⟩⟨ψ| satisfies S(ρ) = 0.

**Why pure states have zero entropy:**

The density operator |ψ⟩⟨ψ| is a rank-1 projector onto span{|ψ⟩}. Its
spectral decomposition is trivial:
  - Eigenvalue 1 for eigenvector |ψ⟩ (since |ψ⟩⟨ψ|ψ⟩ = |ψ⟩)
  - Eigenvalue 0 for any |φ⟩ ⊥ |ψ⟩ (since |ψ⟩⟨ψ|φ⟩ = 0)

Thus eigenvalues are (1, 0, ..., 0) and S = η(1) + η(0) + ... = 0.

**Physical interpretation:**

A pure state represents maximal knowledge about a quantum system.
The experimenter knows exactly which state |ψ⟩ was prepared — there
is no classical uncertainty about which quantum state the system is in.

Zero entropy reflects this certainty. Compare:
  - Pure state |ψ⟩: "The system is definitely in state |ψ⟩" → S = 0
  - Mixed state: "The system is in |ψ₁⟩ or |ψ₂⟩, I don't know which" → S > 0

**Subtlety — quantum vs classical uncertainty:**

Even pure states exhibit measurement uncertainty (Heisenberg). The entropy
S(ρ) does not measure this intrinsic quantum randomness. Rather, it measures
our classical ignorance about which pure state the system occupies.

This distinction is crucial: a pure state has S = 0 despite yielding
probabilistic measurement outcomes. The entropy quantifies mixedness
of the state preparation, not quantum indeterminacy.

**Proof:**

Applies `fromPure_eigenvalues` (axiom giving eigenvalue structure of |ψ⟩⟨ψ|)
then `entropy_of_pure_eigenvalues` (direct calculation for delta distribution).
-/
theorem entropy_pure {n : ℕ} (ψ : QuantumState (ℂ^n)) (hn : 0 < n) :
    S(fromPure ψ) = 0 := by
  obtain ⟨i₀, hi₀_one, hi₀_rest⟩ := fromPure_eigenvalues ψ hn
  exact entropy_of_pure_eigenvalues (fromPure ψ) hn i₀ hi₀_one hi₀_rest



/-- Characterization of extremal probability distributions via sum of squares.

For a probability distribution p : Fin n → ℝ (i.e., pᵢ ≥ 0 and Σᵢ pᵢ = 1):

  Σᵢ pᵢ² = 1  ↔  ∃! i₀, pᵢ₀ = 1 (and pᵢ = 0 for all i ≠ i₀)

**Mathematical content:**

The sum of squares Σᵢ pᵢ² measures concentration of a distribution.
By Cauchy-Schwarz: (Σᵢ pᵢ)² ≤ n · Σᵢ pᵢ², giving Σᵢ pᵢ² ≥ 1/n.

The bounds are:
  - Minimum 1/n: achieved by uniform distribution pᵢ = 1/n
  - Maximum 1: achieved by delta distribution pᵢ₀ = 1, pᵢ = 0 (i ≠ i₀)

**Key insight:** For p ∈ [0,1], we have p² ≤ p with equality iff p ∈ {0,1}.
Thus Σᵢ pᵢ² ≤ Σᵢ pᵢ = 1, with equality iff each pᵢ ∈ {0,1}.
Combined with normalization, exactly one pᵢ = 1.

**Quantum mechanical interpretation:**

This theorem characterizes pure quantum states:
  - Eigenvalues λᵢ of density operator form probability distribution
  - Purity γ = Tr(ρ²) = Σᵢ λᵢ²
  - γ = 1 iff state is pure (single eigenvalue = 1)

The proof proceeds by showing p² = p for all i (from sum equality),
which factors as p(p-1) = 0, forcing each p ∈ {0,1}.
-/
theorem sum_sq_eq_one_iff_singleton {n : ℕ} (_ /-hn-/ : 0 < n) (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_le_one : ∀ i, p i ≤ 1)
    (hp_sum : ∑ i, p i = 1) :
    ∑ i, (p i)^2 = 1 ↔ ∃ i₀, p i₀ = 1 ∧ ∀ i, i ≠ i₀ → p i = 0 := by
  constructor
  · -- Σ pᵢ² = 1 → singleton
    intro hsq
    -- Use: pᵢ ∈ [0,1] implies pᵢ² ≤ pᵢ, with equality iff pᵢ ∈ {0, 1}
    have hsq_le : ∀ i, (p i)^2 ≤ p i := by
      intro i
      have h := hp_nonneg i
      have h' := hp_le_one i
      calc (p i)^2 = p i * p i := sq (p i)
        _ ≤ p i * 1 := by exact mul_le_mul_of_nonneg_left h' h
        _ = p i := mul_one _
    -- Since Σ pᵢ² = 1 = Σ pᵢ and pᵢ² ≤ pᵢ, we have pᵢ² = pᵢ for all i
    have heq : ∀ i, (p i)^2 = p i := by
      have hle : ∑ i, (p i)^2 ≤ ∑ i, p i := Finset.sum_le_sum (fun i _ => hsq_le i)
      rw [hsq, hp_sum] at hle
      -- equality in sum means equality termwise
      by_contra hne
      push_neg at hne
      obtain ⟨j, hj⟩ := hne
      have hstrict : (p j)^2 < p j := lt_of_le_of_ne (hsq_le j) hj
      have hsum_strict : ∑ i, (p i)^2 < ∑ i, p i := by
        apply Finset.sum_lt_sum (fun i _ => hsq_le i)
        exact ⟨j, Finset.mem_univ j, hstrict⟩
      rw [hsq, hp_sum] at hsum_strict
      exact lt_irrefl 1 hsum_strict
    -- pᵢ² = pᵢ means pᵢ(pᵢ - 1) = 0, so pᵢ ∈ {0, 1}
    have h01 : ∀ i, p i = 0 ∨ p i = 1 := by
      intro i
      have h := heq i
      have : p i * (p i - 1) = 0 := by ring_nf; linarith [h]
      rcases mul_eq_zero.mp this with hz | hz
      · left; exact hz
      · right; linarith
    -- Since Σ pᵢ = 1 and each pᵢ ∈ {0, 1}, exactly one is 1
    have hex : ∃ i₀, p i₀ = 1 := by
      by_contra hall
      push_neg at hall
      have : ∀ i, p i = 0 := by
        intro i
        rcases h01 i with h | h
        · exact h
        · exact absurd h (hall i)
      have : ∑ i, p i = 0 := by simp [this]
      rw [hp_sum] at this
      exact one_ne_zero this
    obtain ⟨i₀, hi₀⟩ := hex
    use i₀, hi₀
    intro i hne
    rcases h01 i with h | h
    · exact h
    · -- Two indices with value 1 contradicts sum = 1
      exfalso
      have hsub : {i₀, i} ⊆ Finset.univ := Finset.subset_univ _
      have hpair : ∑ j ∈ ({i₀, i} : Finset (Fin n)), p j = p i₀ + p i :=
        Finset.sum_pair hne.symm
      have hsum2 : 2 ≤ ∑ j, p j := by
        calc ∑ j, p j
            ≥ ∑ j ∈ {i₀, i}, p j :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hp_nonneg j)
          _ = p i₀ + p i := hpair
          _ = 1 + 1 := by rw [hi₀, h]
          _ = 2 := by ring
      rw [hp_sum] at hsum2
      linarith
  · -- singleton → Σ pᵢ² = 1
    intro ⟨i₀, hi₀, hrest⟩
    calc ∑ i, (p i)^2
        = (p i₀)^2 + ∑ i ∈ Finset.univ.erase i₀, (p i)^2 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      _ = 1^2 + ∑ i ∈ Finset.univ.erase i₀, 0^2 := by
          congr 1
          · rw [hi₀]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [hrest i (Finset.ne_of_mem_erase hi)]
      _ = 1 := by norm_num



/-- Fundamental characterization: von Neumann entropy vanishes iff the state is pure.

  S(ρ) = 0  ↔  ρ is pure

This is the quantum analogue of: Shannon entropy vanishes iff the distribution
is deterministic (concentrated on a single outcome).

**Physical interpretation:**

Von Neumann entropy quantifies quantum uncertainty. Zero entropy means
complete knowledge — the system is in a definite quantum state |ψ⟩,
not a statistical mixture. This is the quantum notion of "certainty."

Conversely, any mixed state has S > 0: incomplete information about
which pure state the system is in manifests as nonzero entropy.

**Proof sketch:**

(→) S(ρ) = 0: Since S = Σᵢ η(λᵢ) with each η(λᵢ) ≥ 0, we have η(λᵢ) = 0
for all i. On [0,1], η(x) = -x ln x = 0 iff x ∈ {0,1}. Combined with
Σᵢ λᵢ = 1, exactly one eigenvalue is 1. Thus purity Σᵢ λᵢ² = 1.

(←) ρ pure: Eigenvalues are (1, 0, ..., 0), so S = η(1) + η(0) + ... = 0.

**Connection to information theory:**

This parallels the classical result: H(X) = 0 iff X is deterministic.
The quantum version is deeper — pure states still have measurement
uncertainty (complementarity), but the state itself is fully specified.

**Role in quantum information:**

- Identifies states with no "missing information"
- Pure states are the resource states for quantum protocols
- Entanglement entropy (S of reduced state) measures entanglement precisely
  because S = 0 picks out unentangled (product) pure states
-/
theorem entropy_zero_iff_pure {n : ℕ} (hn : 0 < n) (ρ : DensityOp n) :
    S(ρ) = 0 ↔ ρ.isPure := by
  constructor
  · -- S(ρ) = 0 → isPure
    intro hS
    unfold vonNeumannEntropy at hS
    -- Each term is non-negative and sums to 0, so each is 0
    have hterms : ∀ i, eta (ρ.eigenvalues i) = 0 := by
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ eta (ρ.eigenvalues i) := by
        intro i _
        exact eta_nonneg (eigenvalues_nonneg ρ i) (eigenvalues_le_one ρ i)
      exact fun i => Finset.sum_eq_zero_iff_of_nonneg hnn |>.mp hS i (Finset.mem_univ i)
    -- Each λᵢ ∈ {0, 1}
    have h01 : ∀ i, ρ.eigenvalues i = 0 ∨ ρ.eigenvalues i = 1 := by
      intro i
      exact (eta_eq_zero_iff (eigenvalues_nonneg ρ i) (eigenvalues_le_one ρ i)).mp (hterms i)
    -- This means Σ λᵢ² = 1 (since exactly one is 1)
    have hpurity : ∑ i, (ρ.eigenvalues i)^2 = 1 := by
      rw [sum_sq_eq_one_iff_singleton hn ρ.eigenvalues]
      rw [← hS]
      rw [hS]
      -- Need to show ∃ i₀ with λᵢ₀ = 1
      have hex : ∃ i₀, ρ.eigenvalues i₀ = 1 := by
        by_contra hall
        push_neg at hall
        have hzero : ∀ i, ρ.eigenvalues i = 0 := by
          intro i
          rcases h01 i with h | h
          · exact h
          · exact absurd h (hall i)
        have : ∑ i, ρ.eigenvalues i = 0 := by simp [hzero]
        rw [eigenvalues_sum_one ρ] at this
        exact one_ne_zero this
      obtain ⟨i₀, hi₀⟩ := hex
      use i₀, hi₀
      intro i hne
      rcases h01 i with h | h
      · exact h
      · -- Two 1s would make sum > 1
        exfalso
        have hsub : {i₀, i} ⊆ Finset.univ := Finset.subset_univ _
        have hpair : ∑ j ∈ ({i₀, i} : Finset (Fin n)), ρ.eigenvalues j =
                    ρ.eigenvalues i₀ + ρ.eigenvalues i := Finset.sum_pair hne.symm
        have : 2 ≤ ∑ j, ρ.eigenvalues j := by
          calc ∑ j, ρ.eigenvalues j
              ≥ ∑ j ∈ {i₀, i}, ρ.eigenvalues j :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => eigenvalues_nonneg ρ j)
            _ = ρ.eigenvalues i₀ + ρ.eigenvalues i := hpair
            _ = 1 + 1 := by rw [hi₀, h]
            _ = 2 := by ring
        rw [eigenvalues_sum_one ρ] at this
        linarith
      exact fun i => eigenvalues_nonneg ρ i
      exact fun i => eigenvalues_le_one ρ i
      exact eigenvalues_sum_one ρ
    -- purity = Σ λᵢ² = 1
    unfold isPure
    rw [purity_eq_sum_sq ρ]
    exact hpurity
  · -- isPure → S(ρ) = 0
    intro hpure
    unfold isPure at hpure
    rw [purity_eq_sum_sq ρ] at hpure
    -- Σ λᵢ² = 1 means exactly one eigenvalue is 1
    rw [sum_sq_eq_one_iff_singleton hn ρ.eigenvalues
        (eigenvalues_nonneg ρ) (eigenvalues_le_one ρ) (eigenvalues_sum_one ρ)] at hpure
    obtain ⟨i₀, hi₀, hrest⟩ := hpure
    exact entropy_of_pure_eigenvalues ρ hn i₀ hi₀ hrest

/-!
=============================================================================================================
## Section 4: Maximally Mixed State
=============================================================================================================

The maximally mixed state ρ = I/n achieves the maximum entropy:

  S(I/n) = ln n

This follows directly from the eigenvalue structure: all eigenvalues
equal 1/n, so:

  S(ρ) = Σᵢ η(1/n) = n · η(1/n) = n · (1/n · ln n) = ln n

The maximally mixed state is the unique state achieving this maximum,
representing complete ignorance about the quantum system.
-/

/-- The maximally mixed state achieves maximum entropy: S(I/n) = ln n.

For the maximally mixed state ρ = I/n on an n-dimensional Hilbert space:
  S(ρ) = ln n

**Derivation:**

The maximally mixed state I/n has all eigenvalues equal to 1/n:
  λ₁ = λ₂ = ... = λₙ = 1/n

Therefore:
  S(I/n) = Σᵢ η(1/n)
         = n · η(1/n)
         = n · (1/n · ln n)     [by `eta_inv`]
         = ln n

**Physical interpretation:**

The maximally mixed state represents complete ignorance about which
basis state the system occupies. Every orthonormal basis is equally
likely — maximal uncertainty, maximal entropy.

This is the quantum analogue of the uniform distribution over n outcomes,
which maximizes Shannon entropy at H = ln n.

**Thermodynamic connection:**

In statistical mechanics, I/n corresponds to:
  - Microcanonical ensemble with n accessible states
  - Infinite temperature limit (all states equally populated)
  - Maximum disorder / minimum information

The entropy S = ln n = k_B ln Ω (with k_B = 1) is exactly Boltzmann's
formula for Ω = n equally probable microstates.

**Uniqueness of maximum:**

The maximally mixed state is the unique density operator achieving
S = ln n. This follows from strict concavity of entropy: any deviation
from uniform eigenvalues strictly decreases entropy.

**Dimensional dependence:**

The maximum entropy ln n grows logarithmically with Hilbert space dimension:
  - n = 2 (qubit): S_max = ln 2 ≈ 0.693 (one nat of information)
  - n = d (qudit): S_max = ln d
  - n → ∞: S_max → ∞ (infinite-dimensional systems can have unbounded entropy)

This logarithmic scaling reflects that entropy counts "effective degrees
of freedom" — doubling the dimension adds one bit of maximum uncertainty.
-/
theorem entropy_maximallyMixed (n : ℕ) (hn : n ≠ 0) :
    S(maximallyMixed n hn) = log n := by
  unfold vonNeumannEntropy
  have hev : ∀ i : Fin n, (maximallyMixed n hn).eigenvalues i = 1 / n :=
    maximallyMixed_eigenvalues n hn
  calc ∑ i : Fin n, eta ((maximallyMixed n hn).eigenvalues i)
      = ∑ i : Fin n, eta (1 / n) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hev i]
    _ = ∑ _i : Fin n, (1 / n) * log n := by
        apply Finset.sum_congr rfl
        intro i _
        exact eta_inv n (Nat.pos_of_ne_zero hn)
    _ = Fintype.card (Fin n) • ((1 / n) * log n) := by
        rw [Finset.sum_const, Finset.card_univ]
    _ = n • ((1 / n) * log n) := by rw [Fintype.card_fin]
    _ = n * ((1 / n) * log n) := by rw [nsmul_eq_mul]
    _ = log n := by field_simp



/-- The maximally mixed state saturates the entropy upper bound.

For n ≥ 1, the state ρ = I/n achieves S(ρ) = ln n, the maximum
possible entropy for an n-dimensional quantum system.

**Context:**

This theorem bridges two results:
  1. `entropy_le_log_dim`: S(ρ) ≤ ln n for all density operators
  2. `entropy_maximallyMixed`: S(I/n) = ln n

Together they establish that I/n is a maximizer of von Neumann entropy.

**Uniqueness (requires concavity):**

Strict concavity of entropy implies I/n is the *unique* maximum:
  - If ρ ≠ I/n, then S(ρ) < ln n strictly
  - The maximum is achieved only by the uniform eigenvalue distribution

This is the quantum maximum entropy principle: among all states
consistent with given constraints, nature chooses the one with
maximum entropy (minimum bias beyond the constraints).

**Information-theoretic meaning:**

Maximum entropy = maximum uncertainty = minimum assumptions.
The state I/n encodes:
  - No preferred basis
  - No preferred outcome in any measurement
  - Complete democracy among all n orthogonal states

Any other state implicitly "knows something" — has lower entropy
because some outcomes are more likely than others.

**Role in quantum information:**

The maximally mixed state serves as:
  - Reference point for measuring correlations (mutual information)
  - Output of complete decoherence / thermalization
  - "Worst case" for many quantum protocols
  - The unique state invariant under all unitary transformations
-/
theorem maximallyMixed_achieves_max_entropy (n : ℕ) (hn : 0 < n) :
    S(maximallyMixed n (Nat.pos_iff_ne_zero.mp hn)) = log n :=
  entropy_maximallyMixed n (Nat.pos_iff_ne_zero.mp hn)



/-- The fundamental bounds on von Neumann entropy.

For any density operator ρ on an n-dimensional Hilbert space (n ≥ 1):

  0 ≤ S(ρ) ≤ ln n

**The complete entropy interval:**

Von Neumann entropy maps the space of density operators to [0, ln n]:
  - Lower bound 0: achieved iff ρ is pure (zero uncertainty)
  - Upper bound ln n: achieved iff ρ = I/n (maximum uncertainty)

Every value in [0, ln n] is achieved by some density operator, and
the map ρ ↦ S(ρ) is continuous (in fact, uniformly continuous on
the compact space of density operators).

**Proof components:**

  - Lower bound: `entropy_nonneg` — sum of non-negative terms
  - Upper bound: `entropy_le_log_dim` — Gibbs' inequality / log-sum inequality

**Tightness:**

Both bounds are saturated:
  - S(|ψ⟩⟨ψ|) = 0 for any pure state (`entropy_pure`)
  - S(I/n) = ln n for maximally mixed state (`entropy_maximallyMixed`)

**Physical interpretation:**

The entropy interval [0, ln n] quantifies the spectrum of knowledge:
  - S = 0: "I know exactly which pure state the system is in"
  - S = ln n: "I have no idea — all basis states equally plausible"
  - 0 < S < ln n: Partial knowledge, some states more likely than others

**Dimensional scaling:**

Maximum entropy ln n grows with Hilbert space dimension:
  - Larger systems can accommodate more uncertainty
  - Each doubling of dimension adds ln 2 ≈ 0.693 nats to the ceiling
  - Reflects the exponential growth of state space in quantum mechanics

**Analogy with classical information:**

For a classical probability distribution over n outcomes:
  0 ≤ H(p) ≤ ln n

The quantum bounds are identical — eigenvalues of ρ form a probability
distribution, and von Neumann entropy reduces to Shannon entropy
in the eigenbasis. The bounds are basis-independent because entropy is.
-/
theorem entropy_bounds (n : ℕ) (hn : 0 < n) (ρ : DensityOp n) :
    0 ≤ S(ρ) ∧ S(ρ) ≤ log n :=
  ⟨entropy_nonneg ρ, entropy_le_log_dim n hn ρ⟩

/-!
=============================================================================================================
## Section 5: Concavity
=============================================================================================================

The von Neumann entropy is concave: for any density operators ρ₁, ρ₂
and probability p ∈ [0, 1]:

  S(pρ₁ + (1-p)ρ₂) ≥ p·S(ρ₁) + (1-p)·S(ρ₂)

Physical interpretation: Mixing states can only increase uncertainty.
Forgetting which state was prepared adds classical uncertainty on top
of the quantum uncertainty in each state.

The proof requires:
  1. Concavity of η(x) = -x ln x on [0, 1]
  2. Relationship between eigenvalues of mixture and original states

This is significantly harder than the bounds proofs and is axiomatized here.
-/

/-- The entropy function η(x) = -x ln x is concave on [0, 1].

For x, y ∈ [0, 1] and t ∈ [0, 1]:
  η(t·x + (1-t)·y) ≥ t·η(x) + (1-t)·η(y)

**Concavity via calculus:**

The second derivative test establishes concavity:
  η(x) = -x ln x
  η'(x) = -ln x - 1
  η''(x) = -1/x < 0  for x > 0

Negative second derivative implies strict concavity on (0, 1].
Extension to [0, 1] follows by continuity at x = 0.

**Geometric meaning:**

The graph of η lies above all its chords. For any two points on
the curve, the straight line connecting them lies entirely below
the curve. This is the ∩-shape characteristic of concave functions.

**Why concavity matters for entropy:**

Concavity of η is the microscopic ingredient yielding:

  1. *Concavity of von Neumann entropy*: S(Σᵢ pᵢρᵢ) ≥ Σᵢ pᵢ S(ρᵢ)
     Mixing states increases entropy.

  2. *Maximum entropy principle*: Among all distributions with given
     constraints, entropy is maximized by the "most uniform" one.
     Concavity ensures the maximum is unique.

  3. *Subadditivity* (ultimately): The entropy inequalities for
     composite systems trace back to concavity arguments.

**Information-theoretic intuition:**

Concavity says: averaging probabilities increases uncertainty.
If you have two distributions and mix them, the result is more
uncertain than the average of the individual uncertainties.

Mixing introduces ambiguity — "which distribution did this sample
come from?" — adding entropy beyond what either source had alone.

**Axiomatization note:**

Proving concavity requires calculus (second derivative) or convex
analysis machinery not yet connected to our development. The result
is standard and uncontroversial — axiomatizing it isolates the
analytic content from the algebraic/quantum structure we focus on.

Derivation path: Import Mathlib's `ConcaveOn` theory and show
η is twice differentiable with η'' < 0 on (0, 1).
-/
axiom eta_concave : ∀ (x y t : ℝ),
    0 ≤ x → x ≤ 1 →
    0 ≤ y → y ≤ 1 →
    0 ≤ t → t ≤ 1 →
    eta (t * x + (1 - t) * y) ≥ t * eta x + (1 - t) * eta y

/-- Von Neumann entropy is concave over the space of density operators.

For density operators ρ₁, ρ₂ and mixing probability p ∈ [0, 1]:

  S(p·ρ₁ + (1-p)·ρ₂) ≥ p·S(ρ₁) + (1-p)·S(ρ₂)

**Physical interpretation:**

Mixing quantum states can only increase entropy. If an experimentalist:
  1. Prepares ρ₁ with probability p
  2. Prepares ρ₂ with probability (1-p)
  3. Forgets which was prepared

The resulting state ρ = p·ρ₁ + (1-p)·ρ₂ has entropy at least as large
as the average entropy p·S(ρ₁) + (1-p)·S(ρ₂).

The excess entropy S(ρ) - [p·S(ρ₁) + (1-p)·S(ρ₂)] ≥ 0 quantifies
the classical uncertainty introduced by forgetting which state was prepared.

**Why this is harder than η concavity:**

For classical distributions, entropy concavity follows directly from
concavity of η(x) = -x ln x applied termwise.

For quantum states, the eigenvalues of p·ρ₁ + (1-p)·ρ₂ are NOT simple
combinations of eigenvalues of ρ₁ and ρ₂ — matrices don't diagonalize
in the same basis generically. The proof requires:

  - Eigenvalue perturbation theory, or
  - Klein's inequality: Tr(ρ ln ρ - ρ ln σ) ≥ 0, or
  - Joint convexity of quantum relative entropy

This is genuinely harder than the classical case.

**Consequences:**

1. *Mixing increases uncertainty*: Forgetting information costs entropy.

2. *Maximum entropy uniqueness*: Strict concavity implies I/n is the
   unique entropy maximizer — any other state can be "averaged toward"
   I/n to increase entropy.

3. *Data processing inequality*: Quantum channels (CPTP maps) cannot
   decrease entropy on average, traced back to concavity.

4. *Holevo bound*: The classical information extractable from quantum
   states is bounded, with concavity as a key ingredient.

**Equality condition:**

S(p·ρ₁ + (1-p)·ρ₂) = p·S(ρ₁) + (1-p)·S(ρ₂) iff ρ₁ and ρ₂ have
orthogonal support (live in orthogonal subspaces). In this case,
mixing is "classical" — no quantum interference between the states.

**Axiomatization note:**

The proof requires either:
  - Matrix analysis (eigenvalue inequalities for sums)
  - Operator convexity of x ln x
  - Relative entropy machinery

These tools require substantial setup beyond our current infrastructure.
The result is fundamental and well-established — axiomatizing it
cleanly separates analytic machinery from quantum structure.

Standard reference: Nielsen & Chuang, Theorem 11.10.
-/
axiom entropy_concave {n : ℕ} (ρ₁ ρ₂ : DensityOp n) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    S(mix ρ₁ ρ₂ p hp₀ hp₁) ≥ p * S(ρ₁) + (1 - p) * S(ρ₂)



/-- Mixing preserves a fraction of the original entropy.

For density operators ρ₁, ρ₂ and mixing probability p ∈ (0, 1]:

  S(p·ρ₁ + (1-p)·ρ₂) ≥ p·S(ρ₁)

**Derivation from concavity:**

Starting from concavity:
  S(p·ρ₁ + (1-p)·ρ₂) ≥ p·S(ρ₁) + (1-p)·S(ρ₂)

Since S(ρ₂) ≥ 0 and (1-p) ≥ 0, the second term is non-negative:
  p·S(ρ₁) + (1-p)·S(ρ₂) ≥ p·S(ρ₁)

Combining: S(mixture) ≥ p·S(ρ₁).

**Physical meaning:**

Mixing cannot destroy entropy faster than dilution. If you mix ρ₁
with anything at probability p, you retain at least fraction p of
the original entropy.

This is a one-sided bound — the mixture typically has *more* entropy
than p·S(ρ₁) due to the added classical uncertainty of mixing.

**Special cases:**

- ρ₂ pure (S(ρ₂) = 0): Bound becomes tight in the concavity inequality,
  giving S(mixture) ≥ p·S(ρ₁) with potential equality only if ρ₁ = ρ₂.

- ρ₁ pure (S(ρ₁) = 0): Bound gives S(mixture) ≥ 0, which is trivial.
  The interesting content is that mixing a pure state with anything
  else strictly increases entropy (unless p = 1).

- p → 0: Bound says S(mixture) ≥ 0, recovering non-negativity.

- p = 1: Mixture equals ρ₁, bound says S(ρ₁) ≥ S(ρ₁). ✓

**Symmetric version:**

By symmetry of mixing (swap ρ₁ ↔ ρ₂ and p ↔ 1-p):
  S(p·ρ₁ + (1-p)·ρ₂) ≥ (1-p)·S(ρ₂)

Both bounds hold simultaneously.
-/
theorem entropy_mix_ge_left {n : ℕ} (ρ₁ ρ₂ : DensityOp n) (p : ℝ)
    (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    S(mix ρ₁ ρ₂ p (le_of_lt hp₀) hp₁) ≥ p * S(ρ₁) := by
  have h := entropy_concave ρ₁ ρ₂ p (le_of_lt hp₀) hp₁
  have hS₂ : 0 ≤ S(ρ₂) := entropy_nonneg ρ₂
  have h1p : 0 ≤ 1 - p := by linarith
  calc S(mix ρ₁ ρ₂ p (le_of_lt hp₀) hp₁)
      ≥ p * S(ρ₁) + (1 - p) * S(ρ₂) := h
    _ ≥ p * S(ρ₁) + (1 - p) * 0 := by linarith [mul_nonneg h1p hS₂]
    _ = p * S(ρ₁) := by ring

/-!
=============================================================================================================
## Section 6: Subadditivity and Composite Systems (BLOCKED)
=============================================================================================================


For composite systems ρ_AB on H_A ⊗ H_B, von Neumann entropy satisfies:

**Subadditivity**: S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)
  - Equality iff ρ_AB = ρ_A ⊗ ρ_B (product state)

**Araki-Lieb triangle inequality**: |S(ρ_A) - S(ρ_B)| ≤ S(ρ_AB)
  - Lower bound complementing subadditivity

**Strong subadditivity**: S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)
  - The deepest inequality in quantum information theory
  - Implies subadditivity and Araki-Lieb

**BLOCKED**: Requires Hilbert space tensor products with:
  - Inner product: ⟨a₁ ⊗ b₁, a₂ ⊗ b₂⟩ = ⟨a₁, a₂⟩ · ⟨b₁, b₂⟩
  - Partial trace operation
  - DensityOp on tensor product spaces

-/


/-!
=============================================================================================================
SUMMARY
=============================================================================================================

## What We Built

This file establishes the von Neumann entropy S(ρ) = -Tr(ρ ln ρ) for quantum
density operators on finite-dimensional Hilbert spaces ℂⁿ.

## Theorems (Fully Proven)

**Entropy function η(x) = -x ln x:**
- `eta_zero`: η(0) = 0
- `eta_one`: η(1) = 0
- `eta_nonneg`: x ∈ [0,1] → η(x) ≥ 0
- `eta_eq_zero_iff`: x ∈ [0,1] → (η(x) = 0 ↔ x = 0 ∨ x = 1)
- `eta_inv`: η(1/n) = (1/n) · ln(n)

**Basic bounds:**
- `entropy_nonneg`: S(ρ) ≥ 0
- `entropy_bounds`: 0 ≤ S(ρ) ≤ ln(n)

**Pure state characterization:**
- `entropy_of_pure_eigenvalues`: λ = (1,0,...,0) → S = 0
- `entropy_pure`: S(|ψ⟩⟨ψ|) = 0
- `sum_sq_eq_one_iff_singleton`: Σᵢ pᵢ² = 1 ↔ exactly one pᵢ = 1
- `entropy_zero_iff_pure`: S(ρ) = 0 ↔ ρ is pure

**Maximally mixed state:**
- `entropy_maximallyMixed`: S(I/n) = ln(n)
- `maximallyMixed_achieves_max_entropy`: S(I/n) = ln(n) (alternate form)

**Concavity consequences:**
- `entropy_mix_ge_left`: S(pρ₁ + (1-p)ρ₂) ≥ p·S(ρ₁)

## Axioms (With Justification)

**Upper bound:**
- `entropy_le_log_dim`: S(ρ) ≤ ln(n)
  - Requires Gibbs inequality or log-sum inequality
  - Standard convex analysis, not yet connected to our development

**Concavity:**
- `eta_concave`: η(tx + (1-t)y) ≥ t·η(x) + (1-t)·η(y)
  - Requires second derivative test (η''(x) = -1/x < 0)
  - Pure calculus, orthogonal to quantum content

- `entropy_concave`: S(pρ₁ + (1-p)ρ₂) ≥ p·S(ρ₁) + (1-p)·S(ρ₂)
  - Requires eigenvalue perturbation theory for operator sums
  - Alternatively: Klein's inequality or operator convexity of x ln x
  - Significantly harder than classical entropy concavity

All axioms are standard, physically uncontroversial, and derivable with
additional analytic machinery. They isolate calculus/analysis from the
algebraic quantum structure that is our focus.

## What's Blocked

**Subadditivity family** (Section 6):
  - S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)
  - |S(ρ_A) - S(ρ_B)| ≤ S(ρ_AB)
  - S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)

**Blocker:** Hilbert space tensor products with:
  - Inner product ⟨a₁ ⊗ b₁, a₂ ⊗ b₂⟩ = ⟨a₁,a₂⟩·⟨b₁,b₂⟩
  - Partial trace Tr_B : DensityOp(H_A ⊗ H_B) → DensityOp(H_A)
  - Mathlib's algebraic ⊗ lacks these instances

## Dependencies
```
Mathlib.Analysis.SpecialFunctions.Log.Basic
         │
         ▼
    QHilbert (Hilbert.lean)
    ├── trace, trace_*, BoundedOp
    ├── outerProduct, |ψ⟩⟨φ|
    └── QuantumState
         │
         ▼
    QState (State.lean)
    ├── DensityOp structure
    ├── eigenvalues (via Classical.choose)
    ├── eigenvalues_nonneg/le_one/sum_one
    ├── purity, isPure, linearEntropy
    ├── fromPure, maximallyMixed
    ├── fromPure_eigenvalues, maximallyMixed_eigenvalues (axioms)
    └── mix (convex combinations)
         │
         ▼
    QInformation (VonNeumann.lean) ← YOU ARE HERE
```

## Path Forward

**Immediate extensions (no new infrastructure):**
  - RelativeEntropy.lean: D(ρ||σ) for states on same space
  - Continuity.lean: Fannes-Audenaert inequalities
  - RenyiEntropy.lean: S_α(ρ) = (1/(1-α)) ln Tr(ρ^α)

**After tensor product infrastructure:**
  - ConditionalEntropy.lean: S(A|B) = S(AB) - S(B)
  - MutualInformation.lean: I(A:B) = S(A) + S(B) - S(AB)
  - ReducedDensity.lean: Partial trace, purification
  - Entanglement.lean: Entanglement entropy, measures
  - StrongSubadditivity.lean: The deepest inequality

**Downstream applications:**
  - Holography/EntanglementEntropy/RyuTakayanagi.lean
  - OR/Collapse/QuantumSide/DensityMatrix.lean
  - Information/Thermodynamic/Landauer.lean

## References

[1] von Neumann, J. (1932). "Mathematical Foundations of Quantum Mechanics"
    - Original definition of S(ρ)

[2] Nielsen, M. & Chuang, I. (2000). "Quantum Computation and Quantum Information"
    - Chapter 11: Entropy and information
    - Theorems 11.1-11.10 cover our content

[3] Wilde, M. (2013). "Quantum Information Theory"
    - Chapter 11: Quantum entropy
    - Modern treatment with all proofs

[4] Lieb, E. & Ruskai, M.B. (1973). "Proof of the strong subadditivity..."
    - The hardest theorem we're blocked from

================================================================================
-/
end QInformation
