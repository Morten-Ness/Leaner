import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem sum_piFinset_Icc_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L) {d : ℕ} (hd : d = Fintype.card ι)
    (n : ℕ) (r : ℝ) (hr : r < -d) :
    ∑ p ∈ Fintype.piFinset fun _ : ι ↦ Icc (-n : ℤ) n, ‖∑ i, p i • b i‖ ^ r ≤
      2 * d * 3 ^ (d - 1) * ZLattice.normBound b ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := by
  let s (n : ℕ) := Fintype.piFinset fun i : ι ↦ Icc (-n : ℤ) n
  subst hd
  set d := Fintype.card ι
  have hr' : r < 0 := hr.trans_le (by linarith)
  by_cases hd : d = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd
    simp [hd, hr'.ne]
  replace hd : 1 ≤ d := by rwa [Nat.one_le_iff_ne_zero]
  have hs0 : s 0 = {0} := by ext; simp [s, funext_iff]
  have hs {a b : ℕ} (ha : a ≤ b) : s a ⊆ s b := by grind
  have (k : ℕ) : #(s (k + 1) \ s k) ≤ 2 * d * (2 * k + 3) ^ (d - 1) := by
    simp only [le_add_iff_nonneg_right, zero_le, hs, card_sdiff_of_subset, s, Fintype.card_piFinset,
      Int.card_Icc, prod_const]
    grind [abs_pow_sub_pow_le (α := ℤ) (2 * k + 3) (2 * k + 1) d]
  let ε := ZLattice.normBound b
  have hε : 0 < ε := ZLattice.normBound_pos b
  calc ∑ p ∈ s n, ‖∑ i, p i • b i‖ ^ r
      = ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ‖∑ i, p i • b i‖ ^ r := by
        simp [Finset.sum_eq_sum_range_sdiff _ @hs, hs0, hr'.ne]
    _ ≤ ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ((k + 1) * ε) ^ r := by
        gcongr ∑ k ∈ Finset.range n, ∑ p ∈ (s (k + 1) \ s k), ?_ with k hk v hv
        rw [← Nat.cast_one, ← Nat.cast_add]
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hr'.le
        obtain ⟨j, hj⟩ : ∃ i, v i ∉ Icc (-k : ℤ) k := by simpa [s] using (mem_sdiff.mp hv).2
        refine mul_comm _ ε ▸ ZLattice.le_norm_of_le_abs_repr b _ _ j ?_
        suffices ↑k + 1 ≤ |v j| by simpa [Finsupp.single_apply] using this
        by_contra! H
        rw [Int.lt_add_one_iff, abs_le, ← Finset.mem_Icc] at H
        exact hj H
    _ ≤ ∑ k ∈ range n, ↑(2 * d * (3 * (k + 1)) ^ (d - 1)) * ((k + 1) * ε) ^ r := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        gcongr with k hk
        refine (this _).trans ?_
        gcongr
        lia
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range n, (k + 1) ^ (d - 1) * (k + 1 : ℝ) ^ r := by
        simp_rw [Finset.mul_sum]
        congr with k
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity), mul_pow]
        group
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range n, (↑(k + 1) : ℝ) ^ (d - 1 + r) := by
        congr with k
        rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), Nat.cast_sub hd]
        norm_cast
    _ ≤ 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range (n + 1), (k : ℝ) ^ (d - 1 + r) := by
        gcongr
        rw [Finset.sum_range_succ', le_add_iff_nonneg_right]
        positivity
    _ ≤ 2 * d * 3 ^ (d - 1) * ε ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := by
        gcongr
        refine Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) (Real.summable_nat_rpow.mpr ?_)
        linarith

