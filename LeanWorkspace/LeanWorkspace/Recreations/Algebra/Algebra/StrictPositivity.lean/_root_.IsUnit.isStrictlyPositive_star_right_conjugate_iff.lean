import Mathlib

variable {A : Type*}

variable [Semiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

theorem _root_.IsUnit.isStrictlyPositive_star_right_conjugate_iff {u a : A} (hu : IsUnit u) :
    IsStrictlyPositive (u * a * star u) ↔ IsStrictlyPositive a := by
  simp_rw [IsStrictlyPositive.iff_of_unital, hu.star_right_conjugate_nonneg_iff]
  lift u to Aˣ using hu
  rw [← Units.coe_star, Units.isUnit_mul_units, Units.isUnit_units_mul]

