import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_fract (a : R) : fract (fract a) = fract a := Int.fract_eq_self.2 ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

