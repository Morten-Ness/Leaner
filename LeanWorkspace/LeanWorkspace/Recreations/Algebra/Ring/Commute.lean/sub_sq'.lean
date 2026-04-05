import Mathlib

variable {R : Type u}

variable [CommRing R]

theorem sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
  rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]

