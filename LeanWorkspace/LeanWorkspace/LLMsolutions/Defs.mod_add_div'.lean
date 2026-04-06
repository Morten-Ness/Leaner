import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  simpa [mul_comm] using (EuclideanDomain.mod_add_div m k)
