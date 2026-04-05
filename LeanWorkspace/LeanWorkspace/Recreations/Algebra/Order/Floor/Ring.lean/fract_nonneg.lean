import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_nonneg (a : R) : 0 ≤ fract a := sub_nonneg.2 <| floor_le _

