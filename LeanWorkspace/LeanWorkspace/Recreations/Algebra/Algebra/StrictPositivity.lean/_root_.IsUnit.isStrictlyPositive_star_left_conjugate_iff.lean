import Mathlib

variable {A : Type*}

variable [Semiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

theorem _root_.IsUnit.isStrictlyPositive_star_left_conjugate_iff {u a : A} (hu : IsUnit u) :
    IsStrictlyPositive (star u * a * u) ↔ IsStrictlyPositive a := by
  simpa using hu.star.isStrictlyPositive_star_right_conjugate_iff

