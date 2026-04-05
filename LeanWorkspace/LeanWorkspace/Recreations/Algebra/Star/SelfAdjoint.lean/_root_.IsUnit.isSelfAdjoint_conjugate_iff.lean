import Mathlib

variable {R A : Type*}

variable [Monoid R] [StarMul R]

theorem _root_.IsUnit.isSelfAdjoint_conjugate_iff {a u : R} (hu : IsUnit u) :
    IsSelfAdjoint (u * a * star u) ↔ IsSelfAdjoint a := by
  simp [IsSelfAdjoint, mul_assoc, hu.mul_right_inj, hu.star.mul_left_inj]

