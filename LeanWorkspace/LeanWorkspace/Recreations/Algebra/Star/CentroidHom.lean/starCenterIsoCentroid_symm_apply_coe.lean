import Mathlib

variable {α : Type*}

variable [NonAssocSemiring α] [StarRing α]

theorem starCenterIsoCentroid_symm_apply_coe (T : CentroidHom α) :
    ↑(CentroidHom.starCenterIsoCentroid.symm T) = T 1 := rfl

