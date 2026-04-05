import Mathlib

variable {R A : Type*}

variable [Monoid R] [StarMul R]

theorem _root_.IsUnit.isSelfAdjoint_conjugate_iff' {a u : R} (hu : IsUnit u) :
    IsSelfAdjoint (star u * a * u) ↔ IsSelfAdjoint a := by
  simpa using hu.star.isSelfAdjoint_conjugate_iff

