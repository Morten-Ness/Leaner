import Mathlib

variable {R A : Type*}

variable [AddGroup R] [StarAddMonoid R]

theorem star_val_eq {x : selfAdjoint R} : star (x : R) = x := x.prop

