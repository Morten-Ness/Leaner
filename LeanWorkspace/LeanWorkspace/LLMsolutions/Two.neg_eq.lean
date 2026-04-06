FAIL
import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem neg_eq (x : R) : -x = x := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero (R := R) 2
  apply eq_neg_of_add_eq_zero_left
  calc
    x + x = (1 + 1) * x := by rw [add_mul, one_mul, one_mul]
    _ = (2 : R) * x := by norm_num
    _ = 0 * x := by rw [h2]
    _ = 0 := by simp
