import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.of_mul_right_left (H : IsRelPrime x (y * z)) : IsRelPrime x y := by
  rw [isRelPrime_comm] at H ⊢
  exact H.of_mul_left_left

