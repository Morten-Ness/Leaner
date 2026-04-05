import Mathlib

variable {R ι : Type*}

variable [CommSemiring R] [CharP R 2]

theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  rw [← pow_two, ← pow_two, ← pow_two, CharTwo.add_sq]

