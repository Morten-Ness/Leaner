import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  simpa [mul_comm] using EuclideanDomain.div_add_mod m k
