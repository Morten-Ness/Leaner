import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem abs_fract : |fract a| = fract a := abs_eq_self.mpr <| Int.fract_nonneg a

