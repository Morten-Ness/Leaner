import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.of_mul_left_right (H : IsRelPrime (x * y) z) : IsRelPrime y z := (mul_comm x y ▸ H).of_mul_left_left

