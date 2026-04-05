import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b n : ℤ} {x : R}

theorem cast_one_le_of_pos (h : 0 < a) : (1 : R) ≤ a := mod_cast Int.add_one_le_of_lt h

