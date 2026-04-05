import Mathlib

variable {α : Type u}

theorem CanonicallyOrderedMul.toIsOrderedMonoid
    [CommMonoid α] [Preorder α] [CanonicallyOrderedMul α] : IsOrderedMonoid α where
  mul_le_mul_left _ _ := mul_le_mul_left

