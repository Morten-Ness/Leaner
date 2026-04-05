import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact EuclideanDomain.div_add_mod _ _

