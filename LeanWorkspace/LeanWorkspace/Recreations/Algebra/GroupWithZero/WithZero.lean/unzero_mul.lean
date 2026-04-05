import Mathlib

variable {α β γ : Type*}

variable [Mul α]

theorem unzero_mul {x y : WithZero α} (hxy : x * y ≠ 0) :
    unzero hxy = unzero (left_ne_zero_of_mul hxy) * unzero (right_ne_zero_of_mul hxy) := by
  simp only [← coe_inj, coe_mul, coe_unzero]

