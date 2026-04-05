import Mathlib

open scoped Ring

variable {R : Type*}

variable [NonUnitalNonAssocSemiring R] (x : AddUnits R) (y : R)

theorem AddUnits.neg_mulRight : -(x.mulRight y) = (-x).mulRight y := rfl

