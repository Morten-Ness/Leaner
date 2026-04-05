import Mathlib

variable {α : Type*}

variable [NonAssocSemiring α] [StarRing α]

theorem starCenterIsoCentroid_apply (a : ↥(NonUnitalStarSubsemiring.center α)) :
    CentroidHom.starCenterIsoCentroid a = CentroidHom.starCenterToCentroid a := rfl

