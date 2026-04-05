import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem abs_one_sub_fract : |1 - fract a| = 1 - fract a := abs_eq_self.mpr <| sub_nonneg.mpr (Int.fract_lt_one a).le

