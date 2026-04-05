import Mathlib

variable {α β : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv]
  {f g : ℕ → β} {a : ℕ → α}

theorem _root_.cauchy_product (ha : IsCauSeq abs fun m ↦ ∑ n ∈ range m, abv (f n))
    (hb : IsCauSeq abv fun m ↦ ∑ n ∈ range m, g n) (ε : α) (ε0 : 0 < ε) :
    ∃ i : ℕ, ∀ j ≥ i,
      abv ((∑ k ∈ range j, f k) * ∑ k ∈ range j, g k -
        ∑ n ∈ range j, ∑ m ∈ range (n + 1), f m * g (n - m)) < ε := by
  let ⟨P, hP⟩ := ha.bounded
  let ⟨Q, hQ⟩ := hb.bounded
  have hP0 : 0 < P := lt_of_le_of_lt (abs_nonneg _) (hP 0)
  have hPε0 : 0 < ε / (2 * P) := div_pos ε0 (mul_pos (show (2 : α) > 0 by simp) hP0)
  let ⟨N, hN⟩ := hb.cauchy₂ hPε0
  have hQε0 : 0 < ε / (4 * Q) :=
    div_pos ε0 (mul_pos (show (0 : α) < 4 by simp) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0)))
  let ⟨M, hM⟩ := ha.cauchy₂ hQε0
  refine ⟨2 * (max N M + 1), fun K hK ↦ ?_⟩
  have h₁ :
    (∑ m ∈ range K, ∑ k ∈ range (m + 1), f k * g (m - k)) =
      ∑ m ∈ range K, ∑ n ∈ range (K - m), f m * g n := by
    simpa using sum_range_diag_flip K fun m n ↦ f m * g n
  have h₂ :
    (fun i ↦ ∑ k ∈ range (K - i), f i * g k) = fun i ↦ f i * ∑ k ∈ range (K - i), g k := by
    simp [Finset.mul_sum]
  have h₃ :
    ∑ i ∈ range K, f i * ∑ k ∈ range (K - i), g k =
      ∑ i ∈ range K, f i * (∑ k ∈ range (K - i), g k - ∑ k ∈ range K, g k) +
        ∑ i ∈ range K, f i * ∑ k ∈ range K, g k := by
    rw [← sum_add_distrib]; simp [(mul_add _ _ _).symm]
  have two_mul_two : (4 : α) = 2 * 2 := by norm_num
  have hQ0 : Q ≠ 0 := fun h ↦ by simp [h] at hQε0
  have h2Q0 : 2 * Q ≠ 0 := mul_ne_zero two_ne_zero hQ0
  have hε : ε / (2 * P) * P + ε / (4 * Q) * (2 * Q) = ε := by
    rw [← div_div, div_mul_cancel₀ _ (Ne.symm (ne_of_lt hP0)), two_mul_two, mul_assoc, ← div_div,
      div_mul_cancel₀ _ h2Q0, add_halves]
  have hNMK : max N M + 1 < K :=
    lt_of_lt_of_le (by rw [two_mul]; exact lt_add_of_pos_left _ (Nat.succ_pos _)) hK
  have hKN : N < K :=
    calc
      N ≤ max N M := le_max_left _ _
      _ < max N M + 1 := Nat.lt_succ_self _
      _ < K := hNMK
  have hsumlesum :
      (∑ i ∈ range (max N M + 1),
        abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) ≤
      ∑ i ∈ range (max N M + 1), abv (f i) * (ε / (2 * P)) := by
    gcongr with m hmJ
    refine le_of_lt <| hN (K - m) (le_tsub_of_add_le_left <| hK.trans' ?_) K hKN.le
    rw [two_mul]
    gcongr
    · exact (mem_range.1 hmJ).le
    · exact Nat.le_succ_of_le (le_max_left _ _)
  have hsumltP : (∑ n ∈ range (max N M + 1), abv (f n)) < P :=
    calc
      (∑ n ∈ range (max N M + 1), abv (f n)) = |∑ n ∈ range (max N M + 1), abv (f n)| :=
        Eq.symm (abs_of_nonneg (sum_nonneg fun x _ ↦ abv_nonneg abv (f x)))
      _ < P := hP (max N M + 1)
  rw [h₁, h₂, h₃, sum_mul, ← sub_sub, sub_right_comm, sub_self, zero_sub, abv_neg abv]
  refine lt_of_le_of_lt (IsAbsoluteValue.abv_sum _ _ _) ?_
  suffices
    (∑ i ∈ range (max N M + 1),
          abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) +
        ((∑ i ∈ range K, abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) -
          ∑ i ∈ range (max N M + 1),
            abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) <
      ε / (2 * P) * P + ε / (4 * Q) * (2 * Q) by
    rw [hε] at this
    simpa [abv_mul abv] using this
  gcongr
  · exact lt_of_le_of_lt hsumlesum
        (by rw [← sum_mul, mul_comm]; gcongr)
  rw [sum_range_sub_sum_range (le_of_lt hNMK)]
  calc
    (∑ i ∈ range K with max N M + 1 ≤ i,
          abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) ≤
        ∑ i ∈ range K with max N M + 1 ≤ i, abv (f i) * (2 * Q) := by
        gcongr
        rw [sub_eq_add_neg]
        grw [abv_add abv]
        rw [two_mul, abv_neg abv]
        gcongr <;> exact le_of_lt (hQ _)
    _ < ε / (4 * Q) * (2 * Q) := by
        rw [← sum_mul, ← sum_range_sub_sum_range (le_of_lt hNMK)]
        have := lt_of_le_of_lt (abv_nonneg _ _) (hQ 0)
        gcongr
        exact (le_abs_self _).trans_lt <|
          hM _ ((Nat.le_succ_of_le (le_max_right _ _)).trans hNMK.le) _ <|
            Nat.le_succ_of_le <| le_max_right _ _

