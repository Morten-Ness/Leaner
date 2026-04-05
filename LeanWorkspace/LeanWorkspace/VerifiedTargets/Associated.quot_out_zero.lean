import Mathlib

variable {M : Type*}

variable [MonoidWithZero M]

theorem quot_out_zero : Quot.out (0 : Associates M) = 0 := by rw [← Associates.mk_eq_zero, Associates.quot_out]

