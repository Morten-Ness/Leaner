import Mathlib

variable {α : Type*}

variable [NonUnitalNonAssocSemiring α] [StarRing α]

theorem starCenterToCentroid_apply (z : NonUnitalStarSubsemiring.center α) (a : α) :
    (CentroidHom.starCenterToCentroid z) a = z * a := rfl

