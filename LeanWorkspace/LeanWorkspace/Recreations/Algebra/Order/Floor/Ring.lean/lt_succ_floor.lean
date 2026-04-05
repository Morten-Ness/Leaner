import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem lt_succ_floor (a : R) : a < ⌊a⌋.succ := floor_lt.1 <| Int.lt_succ_self _

