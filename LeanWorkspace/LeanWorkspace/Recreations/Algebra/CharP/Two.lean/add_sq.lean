import Mathlib

variable {R ι : Type*}

variable [CommSemiring R] [CharP R 2]

theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  simp [add_pow_two]

