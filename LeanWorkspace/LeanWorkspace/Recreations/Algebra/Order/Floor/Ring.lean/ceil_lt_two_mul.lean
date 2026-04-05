import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {a b : k}

theorem ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉ < 2 * a := Int.ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

