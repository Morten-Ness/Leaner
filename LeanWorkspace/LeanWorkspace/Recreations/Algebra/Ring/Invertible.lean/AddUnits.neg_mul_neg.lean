import Mathlib

open scoped Ring

variable {R : Type*}

variable [NonUnitalNonAssocSemiring R] (x : AddUnits R) (y : R)

theorem AddUnits.neg_mul_neg {x y : AddUnits R} : ↑(-x) * ↑(-y) = (x * y : R) := by
  rw [← val_mulLeft, ← val_mulLeft, ← AddUnits.ext_iff, ← neg_inj, ← y.neg_mulLeft, neg_neg]
  apply AddUnits.ext
  simp [neg_mul_eq_mul_neg]

