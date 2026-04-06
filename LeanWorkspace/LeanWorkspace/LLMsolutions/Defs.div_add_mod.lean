import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem div_add_mod (a b : R) : b * (a / b) + a % b = a := by
  simpa [mul_comm] using (EuclideanDomain.div_add_mod a b)
