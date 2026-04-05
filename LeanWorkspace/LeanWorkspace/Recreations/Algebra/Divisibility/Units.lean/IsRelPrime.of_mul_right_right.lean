import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.of_mul_right_right (H : IsRelPrime x (y * z)) : IsRelPrime x z := (mul_comm y z ▸ H).of_mul_right_left

