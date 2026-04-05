import Mathlib

variable {R : Type u}

variable [CommRing R]

theorem sub_sq_comm (a b : R) : (a - b) ^ 2 = (b - a) ^ 2 := by
  rw [sub_sq', mul_right_comm, add_comm, sub_sq']

