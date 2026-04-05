import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_ne_zero_iff {a : R} : fract a ≠ 0 ↔ a ∉ Set.range Int.cast := Int.fract_eq_zero_iff.not

