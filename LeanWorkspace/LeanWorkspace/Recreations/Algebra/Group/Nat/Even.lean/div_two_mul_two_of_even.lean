import Mathlib

variable {m n : ℕ}

theorem div_two_mul_two_of_even : Even n → n / 2 * 2 = n := fun h ↦ Nat.div_mul_cancel ((even_iff_exists_two_nsmul _).1 h)

