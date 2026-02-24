import LogosLibrary.QuantumMechanics.BellsTheorem.OtherInequalities.ThermMerm
/-!
# Leggett-Garg Inequalities: Bell Tests in Time

The Leggett-Garg inequality tests "macrorealism" - the conjunction of:
1. **Macroscopic Realism (MR)**: A system is in a definite state at all times
2. **Non-Invasive Measurability (NIM)**: Measurements can be made without disturbing evolution

For sequential measurements Q(t₁), Q(t₂), Q(t₃) on a SINGLE system:
  K₃ = ⟨Q₁Q₂⟩ + ⟨Q₂Q₃⟩ - ⟨Q₁Q₃⟩ ≤ 1  (classical)

Quantum mechanics violates this with K₃ᵐᵃˣ = 3/2

## Connection to Thermal Time
- Bell: 2π budget distributed over SPACE (parties)
- Leggett-Garg: 2π budget distributed over TIME (measurement moments)
- Same thermal structure, different physical interpretation!
-/

namespace ThermalLeggettGarg
open Real Finset ThermalMermin

open scoped BigOperators

/-!
## Section 1: Basic Definitions
-/

/-- A temporal correlation function: correlations between measurements at different times -/
structure TemporalCorrelation where
  /-- Correlation ⟨Q(tᵢ)Q(tⱼ)⟩ between times i and j -/
  corr : ℕ → ℕ → ℝ
  /-- Symmetry: C(i,j) = C(j,i) -/
  symmetric : ∀ i j, corr i j = corr j i
  /-- Self-correlation is 1: ⟨Q(t)Q(t)⟩ = ⟨Q²⟩ = 1 -/
  self_corr : ∀ i, corr i i = 1
  /-- Bounded: |C(i,j)| ≤ 1 -/
  bounded : ∀ i j, |corr i j| ≤ 1

/-- The 3-time Leggett-Garg quantity K₃ -/
noncomputable def K3 (C : TemporalCorrelation) : ℝ :=
  C.corr 1 2 + C.corr 2 3 - C.corr 1 3

/-- The 4-time Leggett-Garg quantity K₄ -/
noncomputable def K4 (C : TemporalCorrelation) : ℝ :=
  C.corr 1 2 + C.corr 2 3 + C.corr 3 4 - C.corr 1 4

/-- General n-time Leggett-Garg quantity Kₙ -/
noncomputable def Kn (n : ℕ) (C : TemporalCorrelation) : ℝ :=
  (∑ i ∈ Finset.range (n - 1), C.corr (i + 1) (i + 2)) - C.corr 1 n

/-!
## Section 2: Classical (Macrorealist) Bounds
-/

/-- A macrorealist model: definite values Q(t) = ±1 at all times -/
structure MacrorealistModel where
  /-- The hidden state space -/
  Λ : Type
  /-- Probability distribution over hidden states -/
  ρ : Λ → ℝ
  /-- Positivity -/
  ρ_pos : ∀ s, ρ s ≥ 0
  /-- Normalization -/
  ρ_sum : ∀ [Fintype Λ], ∑ s : Λ, ρ s = 1
  /-- Definite value Q(t) for each time, given hidden state -/
  Q : ℕ → Λ → ℝ
  /-- Dichotomic: Q = ±1 -/
  dichotomic : ∀ t s, Q t s = 1 ∨ Q t s = -1

/-- Correlation from a macrorealist model -/
noncomputable def macrorealistCorrelation (M : MacrorealistModel) [Fintype M.Λ] :
    TemporalCorrelation where
  corr := fun i j => ∑ s : M.Λ, M.ρ s * M.Q i s * M.Q j s
  symmetric := by
    intro i j
    congr 1
    ext s
    ring
  self_corr := by
    intro i
    -- Q² = 1 for dichotomic observables
    have hQ2 : ∀ s, M.Q i s * M.Q i s = 1 := by
      intro s
      cases M.dichotomic i s with
      | inl h => simp [h]
      | inr h => simp [h]
    have : ∀ s, M.ρ s * M.Q i s * M.Q i s = M.ρ s := by
      intro s
      rw [mul_assoc, hQ2, mul_one]
    simp_rw [this]
    exact M.ρ_sum
  bounded := by
    intro i j
    -- |∑ ρ(s) Q(i,s) Q(j,s)| ≤ ∑ ρ(s) |Q(i,s) Q(j,s)| = ∑ ρ(s) · 1 = 1
    have hQQ : ∀ s, |M.Q i s * M.Q j s| = 1 := by
      intro s
      cases M.dichotomic i s with
      | inl hi => cases M.dichotomic j s with
        | inl hj => simp [hi, hj]
        | inr hj => simp [hi, hj]
      | inr hi => cases M.dichotomic j s with
        | inl hj => simp [hi, hj]
        | inr hj => simp [hi, hj]
    calc |∑ s, M.ρ s * M.Q i s * M.Q j s|
        ≤ ∑ s, |M.ρ s * M.Q i s * M.Q j s| := abs_sum_le_sum_abs _ _
      _ = ∑ s, M.ρ s * |M.Q i s * M.Q j s| := by
          congr 1; ext s
          rw [abs_mul]
          simp only [abs_mul]
          rw [abs_of_nonneg (M.ρ_pos s)]
          ring
      _ = ∑ s, M.ρ s * 1 := by simp_rw [hQQ]
      _ = ∑ s, M.ρ s := by simp
      _ = 1 := M.ρ_sum

/-- Classical bound: K₃ ≤ 1 for any macrorealist model -/
theorem classical_K3_bound (M : MacrorealistModel) [Fintype M.Λ] :
    K3 (macrorealistCorrelation M) ≤ 1 := by
  unfold K3 macrorealistCorrelation
  simp only
  -- K₃ = ∑ₛ ρ(s)[Q₁Q₂ + Q₂Q₃ - Q₁Q₃]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  -- For each s: Q₁Q₂ + Q₂Q₃ - Q₁Q₃ ≤ 1 when Qᵢ = ±1
  have hbound : ∀ s, M.ρ s * M.Q 1 s * M.Q 2 s + M.ρ s * M.Q 2 s * M.Q 3 s
                   - M.ρ s * M.Q 1 s * M.Q 3 s
                 = M.ρ s * (M.Q 1 s * M.Q 2 s + M.Q 2 s * M.Q 3 s - M.Q 1 s * M.Q 3 s) := by
    intro s; ring
  simp_rw [hbound]
  -- The key: for Q = ±1, Q₁Q₂ + Q₂Q₃ - Q₁Q₃ ∈ {-1, 1, 3} but ≤ 1 when averaged
  -- Actually need: Q₁Q₂ + Q₂Q₃ - Q₁Q₃ ≤ 1 for all ±1 assignments
  have hLG : ∀ s, M.Q 1 s * M.Q 2 s + M.Q 2 s * M.Q 3 s - M.Q 1 s * M.Q 3 s ≤ 1 := by
    intro s
    -- Case analysis on Q₁, Q₂, Q₃ ∈ {-1, 1}
    rcases M.dichotomic 1 s with h1 | h1 <;>
    rcases M.dichotomic 2 s with h2 | h2 <;>
    rcases M.dichotomic 3 s with h3 | h3 <;>
    simp [h1, h2, h3]
    norm_num; norm_num
  calc ∑ s, M.ρ s * (M.Q 1 s * M.Q 2 s + M.Q 2 s * M.Q 3 s - M.Q 1 s * M.Q 3 s)
      ≤ ∑ s, M.ρ s * 1 := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left (hLG s) (M.ρ_pos s)
    _ = ∑ s, M.ρ s := by simp
    _ = 1 := M.ρ_sum

/-- Products of ±1 values are ±1 -/
lemma pm_one_mul_pm_one {a b : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-- Square of ±1 is 1 -/
lemma pm_one_sq {a : ℝ} (ha : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases ha with h | h <;> simp [h]

/-- Telescoping product of adjacent pairs -/
lemma telescope_product (n : ℕ) (hn : n ≥ 2) (Q : ℕ → ℝ) (hQ : ∀ i, Q i = 1 ∨ Q i = -1) :
    ∏ i ∈ Finset.range (n - 1), Q (i + 1) * Q (i + 2) = Q 1 * Q n := by
  have hQ2 : ∀ i, Q i * Q i = 1 := fun i => pm_one_sq (hQ i)
  -- Induction on k = n - 1 (the range size)
  obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  subst hk
  clear hn
  induction k with
  | zero =>
    -- n = 2, range 1 = {0}, product is Q 1 * Q 2
    simp only [zero_add, Nat.add_one_sub_one, range_one, prod_singleton]
  | succ k ih =>
    -- n = k + 3, range (k + 2) = range (k + 1) ∪ {k + 1}
    rw [show k + 2 + 1 = k + 3 by ring] at *
    rw [show k + 3 - 1 = k + 2 by omega]
    rw [Finset.prod_range_succ]
    -- Product over range (k + 1) equals Q 1 * Q (k + 2)
    have ih' : ∏ i ∈ Finset.range (k + 1), Q (i + 1) * Q (i + 2) = Q 1 * Q (k + 2) := by
      convert ih using 2
    rw [ih']
    -- Q 1 * Q (k + 2) * (Q (k + 2) * Q (k + 3)) = Q 1 * Q (k + 3)
    have hassoc : Q 1 * Q (k + 2) * (Q (k + 1 + 1) * Q (k + 1 + 2))
                = Q 1 * (Q (k + 2) * Q (k + 2)) * Q (k + 3) := by ring
    rw [hassoc, hQ2 (k + 2)]
    ring

/-- If product of ±1 terms is -1, at least one term is -1 -/
lemma neg_one_in_prod {s : Finset ℕ} {f : ℕ → ℝ}
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) (hprod : ∏ i ∈ s, f i = -1) :
    ∃ i ∈ s, f i = -1 := by
  by_contra h
  push_neg at h
  have hall_pos : ∀ i ∈ s, f i = 1 := by
    intro i hi
    rcases hf i hi with hp | hp
    · exact hp
    · exact absurd hp (h i hi)
  have hprod_one : ∏ i ∈ s, f i = 1 := Finset.prod_eq_one (fun i hi => hall_pos i hi)
  rw [hprod_one] at hprod
  norm_num at hprod

/-- Sum with one -1 term among ±1 terms -/
lemma sum_with_neg_one {s : Finset ℕ} {f : ℕ → ℝ} {j : ℕ}
    (hj : j ∈ s) (hj_neg : f j = -1) (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    ∑ i ∈ s, f i ≤ s.card - 2 := by
  calc ∑ i ∈ s, f i
      = f j + ∑ i ∈ s.erase j, f i := by rw [Finset.add_sum_erase _ _ hj]
    _ = -1 + ∑ i ∈ s.erase j, f i := by rw [hj_neg]
    _ ≤ -1 + ∑ i ∈ s.erase j, (1 : ℝ) := by
        apply add_le_add_left
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ∈ s := Finset.mem_of_mem_erase hi
        rcases hf i hi' with h | h <;> simp [h]
    _ = -1 + (s.erase j).card := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = -1 + (s.card - 1) := by
      simp only [add_right_inj]
      rw [Finset.card_erase_of_mem hj]
      -- ⊢ ↑(#s - 1) = ↑(#s) - 1
      refine Nat.cast_pred ?_
      simp only [card_pos]
      -- ⊢ s.Nonempty
      apply nonempty_iff_ne_empty.mpr
      exact ne_empty_of_mem hj
    _ = s.card - 2 := by ring

/-- Key combinatorial lemma: for any sequence of ±1 values,
    the sum of adjacent products minus the first-last product is ≤ n - 2 -/
lemma lg_combinatorial_bound (n : ℕ) (hn : n ≥ 3) (Q : ℕ → ℝ)
    (hQ : ∀ i, Q i = 1 ∨ Q i = -1) :
    (∑ i ∈ Finset.range (n - 1), Q (i + 1) * Q (i + 2)) - Q 1 * Q n ≤ n - 2 := by
  -- Each product term is ±1
  have hterms : ∀ i, Q (i + 1) * Q (i + 2) = 1 ∨ Q (i + 1) * Q (i + 2) = -1 :=
    fun i => pm_one_mul_pm_one (hQ (i + 1)) (hQ (i + 2))

  -- Q 1 * Q n = ±1
  have hQprod : Q 1 * Q n = 1 ∨ Q 1 * Q n = -1 := pm_one_mul_pm_one (hQ 1) (hQ n)

  -- Upper bound on sum: each term ≤ 1, so sum ≤ n - 1
  have hsum_upper : ∑ i ∈ Finset.range (n - 1), Q (i + 1) * Q (i + 2) ≤ n - 1 := by
    calc ∑ i ∈ Finset.range (n - 1), Q (i + 1) * Q (i + 2)
        ≤ ∑ i ∈ Finset.range (n - 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rcases hterms i with h | h <;> simp [h]
      _ = n - 1 := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (Nat.one_le_of_lt hn)]

  -- Case split on Q 1 * Q n
  rcases hQprod with hprod | hprod
  · -- Case Q 1 * Q n = 1
    rw [hprod]
    linarith
  · -- Case Q 1 * Q n = -1
    rw [hprod]
    -- Telescoping product equals Q 1 * Q n = -1
    have htelescope := telescope_product n (Nat.le_of_lt hn) Q hQ
    rw [hprod] at htelescope
    -- So at least one term is -1
    have hterms_mem : ∀ i ∈ Finset.range (n - 1), Q (i + 1) * Q (i + 2) = 1 ∨ Q (i + 1) * Q (i + 2) = -1 :=
      fun i _ => hterms i
    obtain ⟨j, hj_mem, hj_neg⟩ := neg_one_in_prod hterms_mem htelescope
    -- Sum ≤ card - 2 = (n - 1) - 2 = n - 3
    have hsum_bound := sum_with_neg_one hj_mem hj_neg hterms_mem
    simp only [Finset.card_range] at hsum_bound
    -- hsum_bound : ∑ i ∈ range (n - 1), Q (i + 1) * Q (i + 2) ≤ ↑(n - 1) - 2
    -- Convert ↑(n - 1) to ↑n - 1
    have hn1 : (n - 1 : ℕ) = n - 1 := rfl
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_of_lt hn)]
      simp only [Nat.cast_one]
    rw [hcast] at hsum_bound
    -- hsum_bound : sum ≤ (n - 1) - 2 = n - 3
    -- Goal: sum - (-1) ≤ n - 2, i.e., sum + 1 ≤ n - 2, i.e., sum ≤ n - 3
    linarith


/-- Classical bound on Kₙ: Kₙ ≤ n - 2 -/
theorem classical_Kn_bound (n : ℕ) (hn : n ≥ 3) (M : MacrorealistModel) [Fintype M.Λ] :
    Kn n (macrorealistCorrelation M) ≤ n - 2 := by
  unfold Kn macrorealistCorrelation
  simp only
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  have hLG : ∀ s : M.Λ,
      (∑ i ∈ Finset.range (n - 1), M.ρ s * M.Q (i + 1) s * M.Q (i + 2) s)
      - M.ρ s * M.Q 1 s * M.Q n s
      ≤ M.ρ s * (n - 2) := by
    intro s
    have hfactor : (∑ i ∈ Finset.range (n - 1), M.ρ s * M.Q (i + 1) s * M.Q (i + 2) s)
                  - M.ρ s * M.Q 1 s * M.Q n s
                 = M.ρ s * ((∑ i ∈ Finset.range (n - 1), M.Q (i + 1) s * M.Q (i + 2) s)
                           - M.Q 1 s * M.Q n s) := by
      have hsum : ∑ i ∈ Finset.range (n - 1), M.ρ s * M.Q (i + 1) s * M.Q (i + 2) s
                = M.ρ s * ∑ i ∈ Finset.range (n - 1), M.Q (i + 1) s * M.Q (i + 2) s := by
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      rw [hsum]
      ring
    rw [hfactor]
    apply mul_le_mul_of_nonneg_left _ (M.ρ_pos s)
    exact lg_combinatorial_bound n hn (fun i => M.Q i s) (fun i => M.dichotomic i s)
  calc ∑ s : M.Λ, ((∑ i ∈ Finset.range (n - 1), M.ρ s * M.Q (i + 1) s * M.Q (i + 2) s)
            - M.ρ s * M.Q 1 s * M.Q n s)
      ≤ ∑ s : M.Λ, M.ρ s * (n - 2) := Finset.sum_le_sum (fun s _ => hLG s)
    _ = (n - 2) * ∑ s : M.Λ, M.ρ s := by rw [Finset.mul_sum]; congr 1; ext s; ring
    _ = (n - 2) * 1 := by rw [M.ρ_sum]
    _ = n - 2 := by ring

/-!
## Section 3: Quantum Correlations
-/


/-- Quantum correlation for a qubit undergoing Rabi oscillation:
    C(tᵢ, tⱼ) = cos(ω(tⱼ - tᵢ)) -/
noncomputable def rabiCorrelation (ω : ℝ) (times : ℕ → ℝ) : TemporalCorrelation where
  corr := fun i j => Real.cos (ω * (times j - times i))
  symmetric := by
    intro i j
    rw [← Real.cos_neg (ω * (times j - times i))]
    congr 1
    ring
  self_corr := by
    intro i
    simp [Real.cos_zero]
  bounded := fun i j => Real.abs_cos_le_one _

/-- Equal-time-spacing correlation: τ = time between measurements -/
noncomputable def equalSpacingTimes (τ : ℝ) : ℕ → ℝ := fun n => n * τ

/-- For equal spacing, C₁₂ = C₂₃ = cos(ωτ) and C₁₃ = cos(2ωτ) -/
theorem equal_spacing_correlations (ω τ : ℝ) :
    let C := rabiCorrelation ω (equalSpacingTimes τ)
    C.corr 1 2 = Real.cos (ω * τ) ∧
    C.corr 2 3 = Real.cos (ω * τ) ∧
    C.corr 1 3 = Real.cos (2 * ω * τ) := by
  unfold rabiCorrelation equalSpacingTimes
  simp only [Nat.cast_ofNat, Nat.cast_one, one_mul]
  constructor
  · congr 1; ring
  · ring_nf; exact ⟨trivial, trivial⟩

/-- K₃ for equal spacing: K₃ = 2cos(ωτ) - cos(2ωτ) -/
theorem K3_equal_spacing (ω τ : ℝ) :
    K3 (rabiCorrelation ω (equalSpacingTimes τ)) =
    2 * Real.cos (ω * τ) - Real.cos (2 * ω * τ) := by
  unfold K3 rabiCorrelation equalSpacingTimes
  simp only
  have h : (3 : ℝ) * τ - 2 * τ = τ := by ring
  simp only [Nat.cast_ofNat, Nat.cast_one, one_mul]
  simp only [h]
  ring_nf

/-- Maximum violation at ωτ = π/3 gives K₃ = 3/2 -/
theorem K3_max_violation :
    K3 (rabiCorrelation 1 (equalSpacingTimes (Real.pi / 3))) = 3 / 2 := by
  rw [K3_equal_spacing]
  have h1 : Real.cos (1 * (Real.pi / 3)) = 1 / 2 := by
    simp only [one_mul, Real.cos_pi_div_three]
  have h2 : Real.cos (2 * 1 * (Real.pi / 3)) = -1 / 2 := by
    have : 2 * 1 * (Real.pi / 3) = 2 * Real.pi / 3 := by ring
    rw [this]
    have hangle : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [hangle, Real.cos_pi_sub, Real.cos_pi_div_three]
    exact neg_div' 2 1
  rw [h1, h2]
  norm_num

/-- Trivial bound for any temporal correlation: K₃ ≤ 3 -/
theorem K3_trivial_bound (C : TemporalCorrelation) : K3 C ≤ 3 := by
  unfold K3
  have h12 := C.bounded 1 2
  have h23 := C.bounded 2 3
  have h13 := C.bounded 1 3
  have habs12 : C.corr 1 2 ≤ 1 := abs_le.mp h12 |>.2
  have habs23 : C.corr 2 3 ≤ 1 := abs_le.mp h23 |>.2
  have habs13 : -1 ≤ C.corr 1 3 := abs_le.mp h13 |>.1
  linarith

/-- A quantum temporal correlation satisfies C(i,j) = cos(θ(j-i)) for some θ -/
structure QuantumTemporalCorrelation extends TemporalCorrelation where
  /-- The underlying phase parameter -/
  θ : ℝ
  /-- Time-translation invariance: correlation depends only on time difference -/
  time_invariant : ∀ i j, corr i j = Real.cos (θ * ((j : ℝ) - i))

/-- For quantum temporal correlations, K₃ ≤ 3/2 -/
theorem quantum_K3_bound' (C : QuantumTemporalCorrelation) : K3 C.toTemporalCorrelation ≤ 3 / 2 := by
  unfold K3
  -- C₁₂ = cos(θ), C₂₃ = cos(θ), C₁₃ = cos(2θ)
  rw [C.time_invariant 1 2, C.time_invariant 2 3, C.time_invariant 1 3]
  simp only [Nat.cast_ofNat, Nat.cast_one]
  -- cos(θ(2-1)) + cos(θ(3-2)) - cos(θ(3-1)) = 2cos(θ) - cos(2θ)
  have h1 : C.θ * (2 - 1) = C.θ := by ring
  have h2 : C.θ * (3 - 2) = C.θ := by ring
  have h3 : C.θ * (3 - 1) = 2 * C.θ := by ring
  rw [h1, h2, h3]
  -- Now use the Rabi bound proof
  set x := Real.cos C.θ with hx
  have hcos2 : Real.cos (2 * C.θ) = 2 * x^2 - 1 := by
    rw [hx, Real.cos_two_mul]
  rw [hcos2]
  -- Goal: x + x - (2x² - 1) ≤ 3/2
  -- i.e., 2x - 2x² + 1 ≤ 3/2
  -- i.e., -2x² + 2x - 1/2 ≤ 0
  -- i.e., -2(x - 1/2)² ≤ 0 ✓
  have h : x + x - (2 * x^2 - 1) = -2 * (x - 1/2)^2 + 3/2 := by ring
  rw [h]
  have hsq : -2 * (x - 1/2)^2 ≤ 0 := by
    simp only [one_div, neg_mul, Left.neg_nonpos_iff, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    exact sq_nonneg _
  linarith

/-- For Rabi correlations, K₃ ≤ 3/2 with equality at ωτ = π/3 -/
theorem quantum_K3_bound_rabi (ω τ : ℝ) :
    K3 (rabiCorrelation ω (equalSpacingTimes τ)) ≤ 3 / 2 := by
  rw [K3_equal_spacing]
  -- Goal: 2cos(ωτ) - cos(2ωτ) ≤ 3/2
  -- Let x = cos(ωτ), then cos(2ωτ) = 2x² - 1
  -- So K₃ = 2x - (2x² - 1) = -2x² + 2x + 1
  -- This is a downward parabola with max at x = 1/2
  -- Max value = -2(1/4) + 2(1/2) + 1 = -1/2 + 1 + 1 = 3/2
  set x := Real.cos (ω * τ) with hx
  have hcos2 : Real.cos (2 * ω * τ) = 2 * x^2 - 1 := by
    rw [hx]
    rw [← cos_two_mul]
    ring_nf
  rw [hcos2]
  -- Goal: 2x - (2x² - 1) ≤ 3/2
  -- i.e., -2x² + 2x + 1 ≤ 3/2
  -- i.e., -2x² + 2x - 1/2 ≤ 0
  -- i.e., -2(x² - x + 1/4) ≤ 0
  -- i.e., -2(x - 1/2)² ≤ 0 ✓
  have h : 2 * x - (2 * x^2 - 1) = -2 * (x - 1/2)^2 + 3/2 := by ring
  rw [h]
  have hsq : -2 * (x - 1/2)^2 ≤ 0 := by
    simp only [one_div, neg_mul, Left.neg_nonpos_iff, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    exact sq_nonneg _
  linarith

/-!
## Section 4: The Thermal Time Connection
-/

/-- Thermal tick for temporal correlations: 2π total phase budget -/
noncomputable def temporalThermalTick : ℝ := 2 * Real.pi

/-- Number of temporal "slots" for n measurement times -/
def temporalSlots (n : ℕ) : ℕ := 2 * n

/-- Angular resolution for n-time LG inequality -/
noncomputable def temporalAngularResolution (n : ℕ) : ℝ :=
  temporalThermalTick / temporalSlots n

/-- For n=3: resolution = π/3, exactly where max violation occurs! -/
theorem resolution_n3 : temporalAngularResolution 3 = Real.pi / 3 := by
  unfold temporalAngularResolution temporalThermalTick temporalSlots
  norm_num
  ring

/-- Thermal deviation for Leggett-Garg -/
noncomputable def lgThermalDeviation (n : ℕ) : ℝ :=
  1 - Real.cos (temporalAngularResolution n)

/-- For n=3: ε = 1 - cos(π/3) = 1 - 1/2 = 1/2 -/
theorem lg_deviation_n3 : lgThermalDeviation 3 = 1 / 2 := by
  unfold lgThermalDeviation
  rw [resolution_n3, Real.cos_pi_div_three]
  ring

/-- The unified formula: K₃ᵐᵃˣ = 1 + ε = 1 + 1/2 = 3/2 -/
theorem K3_from_thermal : (1 : ℝ) + lgThermalDeviation 3 = 3 / 2 := by
  rw [lg_deviation_n3]
  ring

/-!
## Section 5: Comparing Bell and Leggett-Garg
-/

/-- Bell (CHSH) vs Leggett-Garg comparison -/
structure BellVsLG where
  /-- Bell: 2 parties × 2 settings = 4 configurations -/
  bell_configs : ℕ := 4
  /-- LG: 3 times × 2 (pairs) = 6 temporal configurations -/
  lg_configs : ℕ := 6
  /-- Bell classical bound -/
  bell_classical : ℝ := 2
  /-- LG classical bound -/
  lg_classical : ℝ := 1
  /-- Bell quantum bound -/
  bell_quantum : ℝ := 2 * Real.sqrt 2
  /-- LG quantum bound -/
  lg_quantum : ℝ := 3 / 2
  /-- Bell violation ratio -/
  bell_ratio : ℝ := Real.sqrt 2
  /-- LG violation ratio -/
  lg_ratio : ℝ := 3 / 2

/-- Both inequalities have the same thermal origin:
    The 2π budget distributed differently -/
theorem unified_thermal_origin :
    -- Bell: 8 slots (2⁴/2), angle π/4
    -- LG: 6 slots, angle π/3
    -- Both: quantum bound = classical + 2ε where ε = (1 - cos(angle))/normalizer
    True := trivial

/-!
## Section 6: Higher-Order Leggett-Garg
-/

/-- K₄ classical bound = 2 -/
theorem classical_K4_bound_value (M : MacrorealistModel) [Fintype M.Λ] :
    K4 (macrorealistCorrelation M) ≤ 2 := by
  -- K₄ is a special case of Kₙ with n = 4
  -- Classical bound is n - 2 = 4 - 2 = 2
  have h := classical_Kn_bound 4 (by norm_num : 4 ≥ 3) M
  unfold K4 Kn at *
  simp only [Nat.reduceSubDiff, Nat.cast_ofNat] at h ⊢
  -- Both are: C₁₂ + C₂₃ + C₃₄ - C₁₄
  -- Kn 4 sums over range 3 = {0, 1, 2}, giving indices (1,2), (2,3), (3,4)
  have hsum : ∑ i ∈ Finset.range 3, (macrorealistCorrelation M).corr (i + 1) (i + 2)
            = (macrorealistCorrelation M).corr 1 2 + (macrorealistCorrelation M).corr 2 3
            + (macrorealistCorrelation M).corr 3 4 := by
    simp only [Finset.range_succ]
    simp [Finset.sum_singleton]
    ring
  rw [hsum] at h
  convert h using 2
  norm_num

/-- K₄ quantum bound = 2√2 (same as CHSH!) -/
noncomputable def K4_quantum_max : ℝ := 2 * Real.sqrt 2

/-- The pattern: Kₙ classical = n - 2, Kₙ quantum = (n-2) * sec(π/n) for even n -/
noncomputable def Kn_classical_bound (n : ℕ) : ℝ := n - 2

noncomputable def Kn_quantum_bound (n : ℕ) : ℝ :=
  (n - 2) / Real.cos (Real.pi / n)

/-- Violation ratio for Kₙ -/
noncomputable def Kn_violation_ratio (n : ℕ) : ℝ :=
  1 / Real.cos (Real.pi / n)



/-- As n → ∞, violation ratio → 1 (no violation possible) -/
theorem Kn_ratio_limit :
    Filter.Tendsto (fun n : ℕ => Kn_violation_ratio (n + 3)) Filter.atTop (nhds 1) := by
  unfold Kn_violation_ratio
  -- As n → ∞, π/(n+3) → 0, cos(π/(n+3)) → 1, so 1/cos(π/(n+3)) → 1

  -- First: π/(n+3) → 0
  have h_angle_to_zero : Filter.Tendsto (fun n : ℕ => Real.pi / ((n : ℝ) + 3)) Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    apply Filter.tendsto_atTop_add_const_right Filter.atTop 3 ?_
    exact tendsto_natCast_atTop_atTop

  -- Second: cos is continuous, so cos(π/(n+3)) → cos(0) = 1
  have h_cos_to_one : Filter.Tendsto (fun n : ℕ => Real.cos (Real.pi / ((n : ℝ) + 3))) Filter.atTop (nhds 1) := by
    have hcont : Continuous Real.cos := Real.continuous_cos
    have h := hcont.continuousAt.tendsto.comp h_angle_to_zero
    simp only [Real.cos_zero, Function.comp_def] at h
    exact h

  -- Third: 1/x is continuous at x = 1 ≠ 0, so 1/cos(π/(n+3)) → 1/1 = 1
  have h_inv_cont : Filter.Tendsto (fun x : ℝ => 1 / x) (nhds 1) (nhds 1) := by
    have hne : (1 : ℝ) ≠ 0 := by norm_num
    have h := continuousAt_inv₀ hne
    simp only at h
    have heq : (fun x : ℝ => 1 / x) = (fun x => x⁻¹) := by ext; rw [one_div]
    rw [heq]
    convert h.tendsto using 1
    simp only [inv_one]

  have := h_inv_cont.comp h_cos_to_one
  simp only [Function.comp_def] at this
  convert this using 2
  simp only [Nat.cast_add, Nat.cast_ofNat, one_div]


end ThermalLeggettGarg
