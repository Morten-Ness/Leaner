import Mathlib

variable {R : Type u}

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]

theorem toIsOrderedMonoid : IsOrderedMonoid R where
  mul_le_mul_left _ _ := mul_le_mul_left

-- TODO: make it an instance

