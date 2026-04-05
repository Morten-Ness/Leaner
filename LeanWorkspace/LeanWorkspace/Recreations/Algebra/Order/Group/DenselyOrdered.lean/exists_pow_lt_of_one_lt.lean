import Mathlib

variable {α : Type*}

variable {M : Type*} [LinearOrder M] [DenselyOrdered M] {x : M}

variable [CommMonoid M] [ExistsMulOfLE M] [IsOrderedCancelMonoid M]

private theorem exists_lt_mul_left [Group α] [LT α] [DenselyOrdered α]
    [MulRightStrictMono α] {a b c : α} (hc : c < a * b) :
    ∃ a' < a, c < a' * b := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul.1 hc'⟩


private theorem exists_lt_mul_right [CommGroup α] [LT α] [DenselyOrdered α]
    [MulLeftStrictMono α] {a b c : α} (hc : c < a * b) :
    ∃ b' < b, c < a * b' := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul'.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul'.1 hc'⟩


private theorem exists_mul_left_lt [Group α] [LT α] [DenselyOrdered α]
    [MulRightStrictMono α] {a b c : α} (hc : a * b < c) :
    ∃ a' > a, a' * b < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt.1 hc'⟩


private theorem exists_mul_right_lt [CommGroup α] [LT α] [DenselyOrdered α]
    [MulLeftStrictMono α] {a b c : α} (hc : a * b < c) :
    ∃ b' > b, a * b' < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt'.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt'.1 hc'⟩


private theorem exists_pow_two_le_of_one_lt (hx : 1 < x) : ∃ y : M, 1 < y ∧ y ^ 2 ≤ x := by
  obtain ⟨y, hy, hyx⟩ := exists_between hx
  obtain hyx | hxy := le_total (y ^ 2) x
  · exact ⟨y, hy, hyx⟩
  obtain ⟨z, hz, rfl⟩ := exists_one_lt_mul_of_lt' hyx
  exact ⟨z, hz, by simpa [pow_succ] using hxy⟩


theorem exists_pow_lt_of_one_lt (hx : 1 < x) : ∀ n : ℕ, ∃ y : M, 1 < y ∧ y ^ n < x
  | 0 => ⟨x, by simpa⟩
  | 1 => by simpa using exists_between hx
  | n + 2 => by
    obtain ⟨y, hy, hyx⟩ := exists_pow_lt_of_one_lt hx (n + 1)
    obtain ⟨z, hz, hzy⟩ := exists_pow_two_le_of_one_lt hy
    refine ⟨z, hz, hyx.trans_le' ?_⟩
    calc z ^ (n + 2)
      _ ≤ z ^ (2 * (n + 1)) := pow_right_monotone hz.le (by lia)
      _ = (z ^ 2) ^ (n + 1) := by rw [pow_mul]
      _ ≤ y ^ (n + 1) := pow_le_pow_left' hzy (n + 1)

