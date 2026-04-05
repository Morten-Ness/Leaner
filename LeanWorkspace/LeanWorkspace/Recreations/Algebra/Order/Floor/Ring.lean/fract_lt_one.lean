import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_lt_one (a : R) : fract a < 1 := sub_lt_comm.1 <| Int.sub_one_lt_floor _

