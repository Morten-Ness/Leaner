import Mathlib

variable {ι : Type*}

variable (A : ι → Type*)

variable [AddZeroClass ι] [GMul A]

theorem GradeZero.smul_eq_mul (a b : A 0) : a • b = a * b := rfl

