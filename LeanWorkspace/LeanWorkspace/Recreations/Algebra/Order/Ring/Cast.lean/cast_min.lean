import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b n : ℤ} {x : R}

theorem cast_min : ↑(min a b) = (min a b : R) := Monotone.map_min Int.cast_mono

