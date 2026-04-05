import Mathlib

variable {M : Type*}

variable [AddMonoid M]

theorem ofAdd_image_setAdd (s t : Set M) :
    ofAdd '' (s + t) = ofAdd '' s * ofAdd '' t := by
  rw [← Set.image2_add, Set.image_image2_distrib ofAdd_add, Set.image2_mul]

