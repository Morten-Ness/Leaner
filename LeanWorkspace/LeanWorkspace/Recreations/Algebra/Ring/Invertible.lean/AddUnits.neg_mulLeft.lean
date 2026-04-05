import Mathlib

open scoped Ring

variable {R : Type*}

variable [NonUnitalNonAssocSemiring R] (x : AddUnits R) (y : R)

theorem AddUnits.neg_mulLeft : -(x.mulLeft y) = (-x).mulLeft y := rfl

