import Mathlib

variable {α : Type*}

variable {M : Type*} [LinearOrder M] [DenselyOrdered M] {x : M}

variable [CommGroup M] [IsOrderedCancelMonoid M]

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


theorem exists_lt_pow_of_lt_one (hx : x < 1) (n : ℕ) : ∃ y : M, y < 1 ∧ x < y ^ n := by
  obtain ⟨y, hy, hy'⟩ := exists_pow_lt_of_one_lt (one_lt_inv_of_inv hx) n
  use y⁻¹, inv_lt_one_of_one_lt hy
  simpa [lt_inv'] using hy'

