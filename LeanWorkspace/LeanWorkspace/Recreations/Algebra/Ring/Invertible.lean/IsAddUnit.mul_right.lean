import Mathlib

open scoped Ring

variable {R : Type*}

variable [NonUnitalNonAssocSemiring R] (x : AddUnits R) (y : R)

theorem IsAddUnit.mul_right {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (x * y) := (h.addUnit.mulRight y).isAddUnit

