import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [One G] [AddCommMonoidWithOne k]

theorem support_one [NeZero (1 : k)] : (1 : SkewMonoidAlgebra k G).support = 1 := Finsupp.support_single_ne_zero _ one_ne_zero

