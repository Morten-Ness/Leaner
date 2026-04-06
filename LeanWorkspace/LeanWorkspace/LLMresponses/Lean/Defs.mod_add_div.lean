import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem mod_add_div (a b : R) : a % b + b * (a / b) = a := by
  simpa [add_comm] using (EuclideanDomain.mod_add_div a b)
