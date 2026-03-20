/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Fourier/ContPoints.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Fourier.Agreement

namespace SpectralBridge.Bochner.FourierUniqueness

open Complex MeasureTheory Filter Topology Set


/-! ## §6.5: Handling atoms — continuity points are dense

For the full theorem, we need `μ(a,b] = ν(a,b]` for ALL `a < b`, not just
at continuity points. A finite measure has at most countably many atoms,
so continuity points of the distribution function are co-countable (hence dense).
We use right-continuity of the distribution function to extend. -/

/-- A finite measure on ℝ has at most countably many atoms. -/
lemma countable_atoms (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Set.Countable {x : ℝ | μ {x} ≠ 0} := by
  apply (Set.countable_iUnion fun n => (finite_of_measure_singleton_ge μ n).countable).mono
  intro x (hx : μ {x} ≠ 0)
  simp only [mem_iUnion, mem_setOf_eq]
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx
  refine ⟨n, le_trans ?_ hn.le⟩
  rw [one_div]
  simp only [ENNReal.inv_le_inv, self_le_add_right]


/-- For any `a : ℝ`, there exist `aₙ < a` with `aₙ → a` and `μ{aₙ} = 0 ∧ ν{aₙ} = 0`.

This is because the set of atoms of `μ` and `ν` is countable, so co-countable
points exist in every interval. -/
lemma exists_continuity_points_below (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a : ℝ) :
    ∃ (seq : ℕ → ℝ), (∀ n, seq n < a) ∧ (∀ n, μ {seq n} = 0) ∧
    (∀ n, ν {seq n} = 0) ∧ Tendsto seq atTop (𝓝 a) := by
  -- Combined atoms are countable
  have h_countable : Set.Countable ({x | μ {x} ≠ 0} ∪ {x | ν {x} ≠ 0}) :=
    (countable_atoms μ).union (countable_atoms ν)
  have h_exists : ∀ n : ℕ, ∃ x ∈ Ioo (a - 1 / (↑n + 1)) a,
      μ {x} = 0 ∧ ν {x} = 0 := by
    intro n
    -- The interval is uncountable
    have h_uncount : ¬ Set.Countable (Ioo (a - 1 / (↑n + 1)) a) := by
      simp only [one_div, Cardinal.Real.Ioo_countable_iff, le_sub_self_iff, inv_nonpos, not_le]
      exact Nat.cast_add_one_pos n
    have h_diff_nonempty : (Ioo (a - 1 / (↑n + 1)) a \
        ({x | μ {x} ≠ 0} ∪ {x | ν {x} ≠ 0})).Nonempty := by
      by_contra h_empty
      have h_sub : Ioo (a - 1 / (↑n + 1)) a ⊆
          {x | μ {x} ≠ 0} ∪ {x | ν {x} ≠ 0} := by
        intro x hx
        by_contra hx'
        exact h_empty ⟨x, hx, hx'⟩
      exact h_uncount (h_countable.mono h_sub)
    obtain ⟨x, hx_Ioo, hx_not_atom⟩ := h_diff_nonempty
    refine ⟨x, hx_Ioo, ?_, ?_⟩
    · simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hx_not_atom
      exact not_ne_iff.mp hx_not_atom.1
    · simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hx_not_atom
      exact not_ne_iff.mp hx_not_atom.2
  -- Use choice to extract the sequence
  choose seq h_seq using h_exists
  refine ⟨seq, ?_, ?_, ?_, ?_⟩
  · intro n; exact (h_seq n).1.2       -- seq n ∈ Ioo ⊢ seq n < a
  · intro n; exact (h_seq n).2.1       -- μ {seq n} = 0
  · intro n; exact (h_seq n).2.2       -- ν {seq n} = 0
  · -- seq n ∈ (a - 1/(n+1), a), so |seq n - a| < 1/(n+1) → 0
    suffices h : Tendsto (fun n => seq n - a) atTop (𝓝 0) by
      have := h.add (tendsto_const_nhds (x := a))
      simp only [sub_add_cancel, zero_add] at this
      exact this
    apply squeeze_zero_norm
    · intro n
      have h_lo := (h_seq n).1.1   -- a - 1/(n+1) < seq n
      have h_hi := (h_seq n).1.2   -- seq n < a
      rw [Real.norm_eq_abs]
    · have h_bound : ∀ n, ‖|seq n - a|‖ ≤ 1 / ((↑n : ℝ) + 1) := by
        intro n
        rw [Real.norm_eq_abs, abs_abs,
            abs_of_nonpos (by linarith [(h_seq n).1.2] : seq n - a ≤ 0)]
        linarith [(h_seq n).1.1]
      have h_tendsto : Tendsto (fun n : ℕ => 1 / ((↑n : ℝ) + 1)) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro δ hδ
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
        refine ⟨N, fun n hn => ?_⟩
        rw [Real.dist_eq, sub_zero,
            abs_of_pos (div_pos one_pos (by positivity : (0 : ℝ) < ↑n + 1))]
        calc (1 : ℝ) / (↑n + 1)
            ≤ 1 / (↑N + 1) := by
              apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ↑N + 1)
              exact_mod_cast Nat.add_le_add_right hn 1
          _ < δ := by rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑N + 1)]
                      rw [← propext (inv_lt_iff_one_lt_mul₀' hδ)]
                      grind only
      exact squeeze_zero_norm h_bound h_tendsto


/-- The distribution function `x ↦ μ(Ioc c x)` for fixed `c` is monotone
    and right-continuous. Two such functions agreeing on a dense set agree everywhere. -/
lemma measure_Ioc_eq_of_fourier_eq' (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ↑ω * ↑t) ∂μ = ∫ ω, exp (I * ↑ω * ↑t) ∂ν)
    (a b : ℝ) (hab : a < b) :
    μ (Ioc a b) = ν (Ioc a b) := by
  -- ── Toolkit ──
  have h_count : Set.Countable ({x | μ {x} ≠ 0} ∪ {x | ν {x} ≠ 0}) :=
    (countable_atoms μ).union (countable_atoms ν)
  -- Any open interval contains a joint non-atom
  have h_na : ∀ x y : ℝ, x < y → ∃ z ∈ Ioo x y, μ {z} = 0 ∧ ν {z} = 0 := by
    intro x y hxy
    by_contra h_none; push_neg at h_none
    have h_sub : Ioo x y ⊆ {z | μ {z} ≠ 0} ∪ {z | ν {z} ≠ 0} := by
      intro z hz
      by_cases hμz : μ {z} = 0
      · exact mem_union_right _ (mem_setOf.mpr (h_none z hz hμz))
      · exact mem_union_left _ (mem_setOf.mpr hμz)
    exact absurd (Cardinal.Real.Ioo_countable_iff.mp (h_count.mono h_sub)) (by linarith)
  -- ── Interval intersection identity ──
  have h_biInter_Ioc : ∀ c d : ℝ,
      ⋂ r, ⋂ (_ : d < r), Ioc c r = Ioc c d := by
    intro c d; ext x; simp only [mem_iInter, mem_Ioc]
    constructor
    · intro hx
      refine ⟨(hx (d + 1) (by linarith)).1, ?_⟩
      by_contra h
      push_neg at h
      obtain ⟨r, hdr, hrx⟩ := exists_between h
      exact absurd (hx r hdr).2 (not_le.mpr hrx)
    · intro ⟨hcx, hxd⟩ r hr
      exact ⟨hcx, hxd.trans hr.le⟩
  -- ── Step A: free right endpoint ──
  -- If c is a joint non-atom, then μ(Ioc c d) = ν(Ioc c d) for ALL d > c
  suffices h_free : ∀ c d : ℝ, μ {c} = 0 → ν {c} = 0 → c < d →
      μ (Ioc c d) = ν (Ioc c d) by
    -- ── Step B: set decomposition ──
    obtain ⟨c, hc_mem, hcμ, hcν⟩ := h_na (a - 1) a (by linarith)
    have hca : c < a := hc_mem.2
    -- μ(Ioc c b) = μ(Ioc c a) + μ(Ioc a b) via Ioc_union_Ioc_eq_Ioc
    have h_union : Ioc c a ∪ Ioc a b = Ioc c b :=
      Ioc_union_Ioc_eq_Ioc hca.le hab.le
    have h_disj : Disjoint (Ioc c a) (Ioc a b) :=
      disjoint_left.mpr fun x hx1 hx2 =>
        absurd (mem_Ioc.mp hx1).2 (not_le.mpr (mem_Ioc.mp hx2).1)
    have hμ_split : μ (Ioc c a) + μ (Ioc a b) = μ (Ioc c b) := by
      rw [← h_union, measure_union h_disj measurableSet_Ioc]
    have hν_split : ν (Ioc c a) + ν (Ioc a b) = ν (Ioc c b) := by
      rw [← h_union, measure_union h_disj measurableSet_Ioc]
    have h1 := h_free c b hcμ hcν (by linarith)
    have h2 := h_free c a hcμ hcν hca
    have key : μ (Ioc c a) + μ (Ioc a b) = μ (Ioc c a) + ν (Ioc a b) :=
      calc μ (Ioc c a) + μ (Ioc a b)
          = μ (Ioc c b) := hμ_split
        _ = ν (Ioc c b) := h1
        _ = ν (Ioc c a) + ν (Ioc a b) := hν_split.symm
        _ = μ (Ioc c a) + ν (Ioc a b) := by rw [← h2]
    exact WithTop.add_left_cancel (measure_ne_top μ (Ioc c a)) key
  -- ── Proof of h_free ──
  intro c d hcμ hcν hcd
  -- μ(Ioc c r) → μ(Ioc c d) as r → d⁺ (by tendsto_measure_biInter_gt)
  have h_lim : ∀ (τ : Measure ℝ) [IsFiniteMeasure τ],
      Tendsto (fun r => τ (Ioc c r)) (𝓝[>] d) (𝓝 (τ (Ioc c d))) := by
    intro τ _
    rw [← h_biInter_Ioc c d]
    exact tendsto_measure_biInter_gt
      (fun r _ => measurableSet_Ioc.nullMeasurableSet)
      (fun _ _ _ hij => Ioc_subset_Ioc_right hij)
      ⟨d + 1, by linarith, measure_ne_top τ _⟩
  -- Construct non-atom sequence rₙ → d⁺
  choose rₙ hrₙ using fun n : ℕ => h_na d (d + 1 / (↑n + 1)) (by
    simp only [one_div, lt_add_iff_pos_right, inv_pos];
    exact Nat.cast_add_one_pos n)
  -- Extract properties
  have hrₙ_gt : ∀ n, d < rₙ n := fun n => (hrₙ n).1.1
  have hrₙ_lt : ∀ n, rₙ n < d + 1 / (↑n + 1) := fun n => (hrₙ n).1.2
  have hrₙ_μ : ∀ n, μ {rₙ n} = 0 := fun n => (hrₙ n).2.1
  have hrₙ_ν : ∀ n, ν {rₙ n} = 0 := fun n => (hrₙ n).2.2
  -- rₙ → d by squeeze
  have hrₙ_lim : Tendsto rₙ atTop (𝓝 d) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => (hrₙ_gt n).le) (fun n => (hrₙ_lt n).le)
    conv_rhs => rw [← add_zero d]
    exact tendsto_const_nhds.add (by
      simp only [one_div]
      exact Filter.Tendsto.inv_tendsto_atTop
        (tendsto_atTop_mono (fun n => le_add_of_nonneg_right zero_le_one)
          tendsto_natCast_atTop_atTop))
  -- rₙ → d in 𝓝[>] d
  have hrₙ_within : Tendsto rₙ atTop (𝓝[>] d) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrₙ_lim, Eventually.of_forall hrₙ_gt⟩
  -- Basic lemma: μ(Ioc c rₙ) = ν(Ioc c rₙ) for all n
  have h_eq : ∀ n, μ (Ioc c (rₙ n)) = ν (Ioc c (rₙ n)) :=
    fun n => measure_Ioc_eq_of_fourier_eq μ ν h (by linarith [hrₙ_gt n])
      hcμ hcν (hrₙ_μ n) (hrₙ_ν n)
  -- Compose: μ(Ioc c rₙ) → μ(Ioc c d) and ν(Ioc c rₙ) → ν(Ioc c d)
  -- Since they agree at each step, limits are equal
  exact tendsto_nhds_unique ((h_lim μ).comp hrₙ_within)
    (((h_lim ν).comp hrₙ_within).congr fun n => (h_eq n).symm)



end SpectralBridge.Bochner.FourierUniqueness
