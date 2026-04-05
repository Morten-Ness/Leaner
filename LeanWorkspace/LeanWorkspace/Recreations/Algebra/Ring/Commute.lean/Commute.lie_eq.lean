import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocRing R]

theorem Commute.lie_eq {x y : R} (h : Commute x y) : ⁅x, y⁆ = 0 := sub_eq_zero_of_eq h

