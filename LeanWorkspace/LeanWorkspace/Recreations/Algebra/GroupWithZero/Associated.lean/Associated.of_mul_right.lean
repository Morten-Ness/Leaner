import Mathlib

variable {M : Type*}

theorem Associated.of_mul_right [CommMonoidWithZero M] [IsCancelMulZero M] {a b c d : M} :
    a * b ~ᵤ c * d → b ~ᵤ d → b ≠ 0 → a ~ᵤ c := by
  rw [mul_comm a, mul_comm c]; exact Associated.of_mul_left

