import Mathlib

variable {R : Type u}

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]

theorem toIsOrderedRing : IsOrderedRing R where
  add_le_add_left _ _ := add_le_add_left

