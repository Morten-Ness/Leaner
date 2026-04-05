import Mathlib

variable {M : Type*}

variable [AddMonoid M]

theorem toAdd_image_setMul (s t : Set (Multiplicative M)) :
    toAdd '' (s * t) = (toAdd '' s) + (toAdd '' t) := by
  rw [← Set.image2_mul, Set.image_image2_distrib toAdd_mul, Set.image2_add]

