import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem ceil_mono : Monotone (ceil : R → ℤ) := gc_ceil_coe.monotone_l

