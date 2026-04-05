import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact EuclideanDomain.mod_add_div _ _

