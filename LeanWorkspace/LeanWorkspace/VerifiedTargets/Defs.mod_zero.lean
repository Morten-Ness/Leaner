import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem mod_zero (a : R) : a % 0 = a := by simpa only [zero_mul, zero_add] using EuclideanDomain.div_add_mod a 0

