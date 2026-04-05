import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b n : ℤ} {x : R}

theorem cast_max : (↑(max a b) : R) = max (a : R) (b : R) := Monotone.map_max Int.cast_mono

