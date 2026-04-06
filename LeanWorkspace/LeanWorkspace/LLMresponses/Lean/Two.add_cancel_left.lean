FAIL
import Mathlib

variable {R ι : Type*}

variable [Semiring R] [CharP R 2]

theorem add_cancel_left (a b : R) : a + (a + b) = b := by
  rw [← add_assoc]
  have h : a + a = 0 := by
    simpa [two_nsmul] using (CharP.cast_eq_zero (R := R) 2)
  rw [h, zero_add]
