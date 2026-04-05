import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocRing R]

theorem commute_iff_lie_eq {x y : R} : Commute x y ↔ ⁅x, y⁆ = 0 := sub_eq_zero.symm

