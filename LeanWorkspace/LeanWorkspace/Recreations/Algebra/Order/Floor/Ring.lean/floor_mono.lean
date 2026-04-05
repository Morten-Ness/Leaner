import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_mono : Monotone (floor : R → ℤ) := gc_coe_floor.monotone_u

