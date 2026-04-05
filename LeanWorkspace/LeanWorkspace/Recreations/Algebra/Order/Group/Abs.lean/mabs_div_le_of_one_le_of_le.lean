import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_le_of_one_le_of_le {a b n : G} (one_le_a : 1 ≤ a) (a_le_n : a ≤ n)
    (one_le_b : 1 ≤ b) (b_le_n : b ≤ n) : |a / b|ₘ ≤ n := by
  rw [mabs_div_le_iff, div_le_iff_le_mul, div_le_iff_le_mul]
  exact ⟨le_mul_of_le_of_one_le a_le_n one_le_b, le_mul_of_le_of_one_le b_le_n one_le_a⟩

