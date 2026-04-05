import Mathlib

open scoped Ring

variable {R : Type*}

variable [NonUnitalNonAssocSemiring R] (x : AddUnits R) (y : R)

theorem IsAddUnit.mul_left {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (y * x) := (h.addUnit.mulLeft y).isAddUnit

