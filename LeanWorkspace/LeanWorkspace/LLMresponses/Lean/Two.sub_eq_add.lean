FAIL
import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem sub_eq_add (x y : R) : x - y = x + y := by
  rw [sub_eq_add_neg]
  congr
  rw [← two_nsmul]
  exact CharP.two_eq_zero y
