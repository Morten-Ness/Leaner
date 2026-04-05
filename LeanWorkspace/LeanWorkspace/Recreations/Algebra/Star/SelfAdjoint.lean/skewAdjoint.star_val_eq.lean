import Mathlib

variable {R A : Type*}

variable [AddCommGroup R] [StarAddMonoid R]

theorem star_val_eq {x : skewAdjoint R} : star (x : R) = -x := x.prop

