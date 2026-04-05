import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [One G] [AddCommMonoidWithOne k]

theorem support_one_subset : (1 : SkewMonoidAlgebra k G).support ⊆ 1 := Finsupp.support_single_subset

