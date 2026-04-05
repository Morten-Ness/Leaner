import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b n : ℤ} {x : R}

theorem cast_abs : (↑|a| : R) = |(a : R)| := by simp [abs_eq_max_neg]

