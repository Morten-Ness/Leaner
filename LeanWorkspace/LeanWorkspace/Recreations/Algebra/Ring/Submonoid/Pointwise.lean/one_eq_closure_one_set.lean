import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoidWithOne R]

theorem one_eq_closure_one_set : (1 : AddSubmonoid R) = closure 1 := AddSubmonoid.one_eq_closure

