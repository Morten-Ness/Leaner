import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem two_eq_zero : (2 : R) = 0 := by
  simpa using (CharP.cast_eq_zero (R := R) 2)
