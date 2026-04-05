import Mathlib

variable {α : Type*}

variable [NonUnitalNonAssocSemiring α] [StarRing α]

theorem star_centerToCentroidCenter (z : NonUnitalStarSubsemiring.center α) :
    star (centerToCentroidCenter z) =
      (centerToCentroidCenter (star z : NonUnitalStarSubsemiring.center α)) := by
  ext a
  calc
      (star (centerToCentroidCenter z)) a = star (z * star a) := rfl
      _ = star (star a) * star z := by simp only [star_mul, star_star, StarMemClass.coe_star]
      _ = a * star z := by rw [star_star]
      _ = (star z) * a := by rw [(star z).property.comm]
      _ = (centerToCentroidCenter ((star z) : NonUnitalStarSubsemiring.center α)) a := rfl

