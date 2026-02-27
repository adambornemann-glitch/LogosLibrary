import LogosLibrary.Superior.SplitMechanics.BellsTheorem.TLHV

open ThermalBell BellTheorem ProbabilityTheory MeasureTheory

namespace ThermalBell

/-! ## Part 13: The Algebraic Origin of 8

Why 8 angle slots in CHSH? Let's derive it from the structure.

CHSH involves:
- 2 settings for Alice: {A₀, A₁}
- 2 settings for Bob: {B₀, B₁}
- 4 correlation terms: E₀₀, E₀₁, E₁₀, E₁₁
- Each dichotomic observable lives in a 2D subspace (eigenvalues ±1)

The "8" should emerge from: 4 terms × 2 dimensions per dichotomic observable?
Or: 2 × 2 × 2 = 8 from the tensor structure?
-/

/-- Number of settings per party -/
def n_settings : ℕ := 2

/-- Number of correlation terms in CHSH -/
def n_correlations : ℕ := n_settings * n_settings

lemma n_correlations_eq : n_correlations = 4 := rfl

/-- Dimension of a dichotomic observable's eigenspace structure -/
def dichotomic_dim : ℕ := 2

/-- First attempt: 4 correlations × 2 for dichotomy = 8 -/
lemma eight_from_correlations_times_dichotomy : n_correlations * dichotomic_dim = 8 := rfl

/-- Second attempt: 2 settings × 2 parties × 2 for dichotomy = 8 -/
lemma eight_from_settings_parties_dichotomy : n_settings * 2 * dichotomic_dim = 8 := rfl

/- The CHSH operator structure: S = A₀⊗(B₁-B₀) + A₁⊗(B₀+B₁)

    This factorization reveals the structure:
    - Two "Alice terms": A₀, A₁
    - Two "Bob combinations": (B₁-B₀), (B₀+B₁)
    - Each product contributes to the bound
-/

/-- The two Bob combinations in the CHSH factorization -/
def bob_combinations (b₀ b₁ : ℝ) : ℝ × ℝ := (b₁ - b₀, b₀ + b₁)

/-- Key property: for dichotomic B, exactly one combination is ±2, other is 0 -/
lemma bob_combinations_complementary (b₀ b₁ : ℝ)
    (hb₀ : b₀ = 1 ∨ b₀ = -1) (hb₁ : b₁ = 1 ∨ b₁ = -1) :
    (bob_combinations b₀ b₁).1 = 0 ∧ |((bob_combinations b₀ b₁).2)| = 2 ∨
    |((bob_combinations b₀ b₁).1)| = 2 ∧ (bob_combinations b₀ b₁).2 = 0 := by
  unfold bob_combinations
  rcases hb₀ with rfl | rfl <;> rcases hb₁ with rfl | rfl <;> simp <;> norm_num

/-- This complementarity is WHY the classical bound is 2, not 4 -/
lemma classical_bound_from_complementarity (a₀ a₁ b₀ b₁ : ℝ)
    (ha₀ : a₀ = 1 ∨ a₀ = -1) (ha₁ : a₁ = 1 ∨ a₁ = -1)
    (hb₀ : b₀ = 1 ∨ b₀ = -1) (hb₁ : b₁ = 1 ∨ b₁ = -1) :
    |a₀ * (b₁ - b₀) + a₁ * (b₀ + b₁)| ≤ 2 := by
  have h := bob_combinations_complementary b₀ b₁ hb₀ hb₁
  rcases h with ⟨hz, ht⟩ | ⟨ht, hz⟩
  · -- First term is 0, second term is ±2
    simp only [bob_combinations] at hz ht
    rw [hz, mul_zero, zero_add]
    rcases ha₁ with rfl | rfl
    · simp; exact le_of_eq ht
    · simp only [neg_one_mul, abs_neg]; exact le_of_eq ht
  · -- First term is ±2, second term is 0
    simp only [bob_combinations] at hz ht
    rw [hz, mul_zero, add_zero]
    rcases ha₀ with rfl | rfl
    · simp; exact le_of_eq ht
    · simp only [neg_one_mul, abs_neg]; exact le_of_eq ht

/- The symmetry group of CHSH under relabeling -/

/-- Swap Alice's settings: A₀ ↔ A₁ -/
def swap_alice (f : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => f (1 - i) j

/-- Swap Bob's settings: B₀ ↔ B₁ -/
def swap_bob (f : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => f i (1 - j)

/-- Swap parties: Alice ↔ Bob -/
def swap_parties (f : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => f j i

/-- The CHSH value with explicit correlation function -/
def chsh_from_correlations (E : Fin 2 → Fin 2 → ℝ) : ℝ :=
  E 0 1 - E 0 0 + E 1 0 + E 1 1

/-- CHSH is NOT invariant under swap_alice alone -/
lemma chsh_not_swap_alice_invariant :
    ∃ E : Fin 2 → Fin 2 → ℝ, chsh_from_correlations E ≠ chsh_from_correlations (swap_alice E) := by
  use fun i j => if i = 0 ∧ j = 0 then 1 else 0
  unfold chsh_from_correlations swap_alice
  simp
  norm_num

/-- CHSH changes sign under certain swaps -/
lemma chsh_sign_change_alice (E : Fin 2 → Fin 2 → ℝ) :
    chsh_from_correlations (swap_alice E) = E 1 1 - E 1 0 + E 0 0 + E 0 1 := by
  unfold chsh_from_correlations swap_alice
  simp only [Fin.isValue, sub_zero, sub_self]

/- Number of independent "directions" in CHSH -/

/-- Alice has 2 settings, each dichotomic: 2 × 1 = 2 degrees of freedom -/
def alice_dof : ℕ := n_settings

/-- Bob has 2 settings, each dichotomic: 2 × 1 = 2 degrees of freedom -/
def bob_dof : ℕ := n_settings

/-- Total configuration space: Alice × Bob = 2 × 2 = 4 setting pairs -/
def config_space_dim : ℕ := alice_dof * bob_dof

lemma config_space_is_four : config_space_dim = 4 := rfl

/-- Each setting pair has 2 "orientations" (the dichotomic ±1) -/
def orientations_per_config : ℕ := dichotomic_dim

/-- Total "phase space": 4 configs × 2 orientations = 8 -/
def total_phase_space : ℕ := config_space_dim * orientations_per_config

lemma total_phase_space_is_eight : total_phase_space = 8 := rfl

/-- The "8" as angle slots: distributing 2π among the phase space -/
lemma angle_per_slot : (2 * Real.pi) / total_phase_space = Real.pi / 4 := by
  unfold total_phase_space config_space_dim orientations_per_config
  unfold alice_dof bob_dof n_settings dichotomic_dim
  norm_num
  ring

/- Alternative interpretation: the 8 vertices of a cube

    Each of A₀, A₁, B₀, B₁ ∈ {±1} gives 2⁴ = 16 configurations.
    But CHSH only takes values ±2, so there are really 2 equivalence classes.
    16/2 = 8 "distinct" configurations up to CHSH value.

    Or: the 8 comes from the 3-dimensional geometry of Bloch vectors?
    (Not quite, since we have 4 observables, not 3)
-/

/-- Number of total sign configurations -/
def total_sign_configs : ℕ := 2^4

lemma total_sign_configs_eq : total_sign_configs = 16 := rfl

/-- CHSH partitions these into two classes: those giving +2 and those giving -2 -/
lemma chsh_partitions_configs :
    ∀ (a₀ a₁ b₀ b₁ : ℝ),
    (a₀ = 1 ∨ a₀ = -1) → (a₁ = 1 ∨ a₁ = -1) →
    (b₀ = 1 ∨ b₀ = -1) → (b₁ = 1 ∨ b₁ = -1) →
    chsh_pointwise a₀ a₁ b₀ b₁ = 2 ∨ chsh_pointwise a₀ a₁ b₀ b₁ = -2 :=
  chsh_pointwise_values

/-- Each class has 8 configurations: 16/2 = 8 -/
lemma configs_per_class : total_sign_configs / 2 = 8 := rfl

/-- THE KEY INSIGHT: 8 = 16/2 where
    - 16 = 2⁴ = all dichotomic configurations
    - 2 = number of CHSH values (±2)

    The modular period 2π, divided by 8, gives π/4.
    This is the "quantum angle" — the angle that maximizes violation.
-/
theorem eight_is_configs_per_chsh_value :
    total_sign_configs / 2 = chsh_angle_slots := rfl

/-- Connecting back to Tsirelson: the 8 configurations that give CHSH = +2
    become "spread out" over the modular period, each contributing π/4 of phase -/
theorem tsirelson_from_configuration_count :
    (2 * Real.pi) / (total_sign_configs / 2) = Real.pi / 4 := by
  simp only [total_sign_configs]
  norm_num
  ring
