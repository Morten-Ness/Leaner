import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem lt_one (a : R) : a ≺ (1 : R) → a = 0 := haveI := Classical.dec
  not_imp_not.1 fun h => by simpa only [one_mul] using mul_left_not_lt 1 h

