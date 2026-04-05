import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_lt_of_one_le_of_lt {a b n : G} (one_le_a : 1 ≤ a) (a_lt_n : a < n)
    (one_le_b : 1 ≤ b) (b_lt_n : b < n) : |a / b|ₘ < n := by
  rw [mabs_div_lt_iff, div_lt_iff_lt_mul, div_lt_iff_lt_mul]
  exact ⟨lt_mul_of_lt_of_one_le a_lt_n one_le_b, lt_mul_of_lt_of_one_le b_lt_n one_le_a⟩

